// the reference implementation is rather complicated
// it uses lots of functors to allow both the solver and api consumer to write as little code as
// possible
// replicating this structure in rust code is looking to be cumbersome, so the api consumer will
// take on a portion of the work, if we can find a way to reduce duplication on that side, it may
// be smart
// the reference implementation also creates a dfagraph which operates on whole basic blocks at
// once to speed things up, this is an optimization that we most definitely want, but we also just
// want any working code to start
use crate::llvm::ast;
use std::collections::{BTreeSet, HashMap};
use std::cmp;
use std::fmt;

// todo: priv the whole thing
pub mod alias;
pub mod constprop;
pub mod dce;
pub mod liveness;

trait DataflowFact<'a> : cmp::PartialEq + fmt::Debug + Sized {
    // for dataflow
    fn combine(facts: &[Self]) -> Self;

    // for dfagraph construction
    fn forward() -> bool;

    /// Describes how a fact flows through an instruction
    fn instruction_flow(self, uid: ast::Uid<'a>, insn: &ast::Insn<'a>) -> Self;
    /// Describes how a fact flows through a terminator
    fn terminator_flow(self, term: &ast::Terminator<'a>) -> Self;
}

trait DFAGraph<'a> {
    type Fact : DataflowFact<'a>;
    type Node : Ord;

    /// Gets the fact flowing out of a node
    fn out(&self, n: &Self::Node) -> Self::Fact;

    /// Gets the predecessors of a node
    fn preds(&self, n: &Self::Node) -> Vec<Self::Node>;
    /// Gets the successors of a node
    fn succs(&self, n: &Self::Node) -> Vec<Self::Node>;
    /// Gets all nodes
    fn nodes(&self) -> Vec<Self::Node>;

    /// Gets the result of flowing a certain fact through a node
    /// pairs well with add_fact
    fn flow(&self, n: &Self::Node, inn: Self::Fact) -> Self::Fact ;
    /// Sets the fact flowing out of a node
    fn add_fact(&mut self, n: &Self::Node, f: Self::Fact);
}

fn solve<'a, T>(mut graph: T) -> T
    where T: DFAGraph<'a>
{
    // todo: which end to remove from? this end gets some small empirical results
    let mut worklist = BTreeSet::from_iter(graph.nodes());
    while let Some(node) = if T::Fact::forward() { worklist.pop_first() } else { worklist.pop_last() } {
        let old_out = graph.out(&node);
        let old_facts: Vec<_> = graph.preds(&node).into_iter().map(|n| graph.out(&n)).collect();
        let inn = DataflowFact::combine(&old_facts);
        let new_out = graph.flow(&node, inn);
        let change = old_out != new_out;
        graph.add_fact(&node, new_out);
        if change {
            worklist.extend(graph.succs(&node));
        }
    }
    graph
}

// these may be the worst names ever
pub struct Analysis<'a, T> {
    map: HashMap<ast::Uid<'a>, usize>,
    vec: Vec<T>,
}

impl<'a, T> Analysis<'a, T> {
    pub fn in_at(&self, uid: ast::Uid<'a>) -> &T {
        &self.vec[self.map[&uid] - 1]
    }

    pub fn out_at(&self, uid: ast::Uid<'a>) -> &T {
        &self.vec[self.map[&uid]]
    }
}

impl<'a, T: fmt::Debug> fmt::Debug for Analysis<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut vals: Vec<_> = self.map.iter().collect();
        vals.sort_by_key(|(_uid, ix)| *ix);
        let vals: Vec<_> = vals.into_iter().map(|(uid, ix)| (uid, &self.vec[*ix])).collect();
        write!(f, "{:?}", vals)
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
enum Node {
    /// regular instruction
    Insn {
        /// index of basic block
        bbix: usize,
        /// index of instruction in
        ix: usize,
    },
    /// terminator instruction
    Term {
        /// index of basic block
        bbix: usize,
    },
    // todo: make this two seperate ones? this would help the ordering a bit which seems to
    // greatly increase the speed of optimizations (at least while we do them per-instruction)
    /// special boundary node representing the edge entering at the top for backward analysis and
    /// an edge at the bottom for forward analysis
    Boundary,
}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

// you can't meaningfully order these because of loops, but a best effort goes a long way for
// improving the dfa solving
impl Ord for Node {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        // todo: this is a hack lol!
        fn to_pair(n: Node) -> (usize, usize) {
            match n {
                Node::Insn { bbix, ix } => (bbix, ix),
                Node::Term { bbix } => (bbix, usize::MAX),
                Node::Boundary => (usize::MAX, usize::MAX),
            }
        }
        to_pair(*self).cmp(&to_pair(*other))
    }
}

#[cfg(test)]
#[test]
fn node_ordering() {
    assert!(Node::Insn { bbix: 0, ix: 0 } < Node::Term { bbix: 0 });
    assert!(Node::Insn { bbix: 0, ix: 0 } < Node::Term { bbix: 1 });
    assert!(Node::Insn { bbix: 1, ix: 0 } > Node::Term { bbix: 0 });
    assert!(Node::Insn { bbix: 0, ix: 0 } < Node::Insn { bbix: 0 , ix: 1 });
    assert!(Node::Insn { bbix: 0, ix: 1 } < Node::Insn { bbix: 1 , ix: 0 });
}

#[derive(Debug)]
struct Graph<'ast, 'fdecl, F> {
    fdecl: &'fdecl ast::Fdecl<'ast>,
    /// map bbix -> [bbix], has a space at the end for the boundary block and at the start for the
    /// entry block
    block_preds: Vec<Vec<usize>>,
    label_to_bbix: HashMap<ast::Lbl<'ast>, usize>,
    facts: HashMap<Node, F>,
}

// todo: clean up + Clone and + Default to be on the trait if needed
impl<'a, 'fdecl, F: DataflowFact<'a> + Default + Clone> Graph<'a, 'fdecl, F> {
    pub fn from_fdecl(fdecl: &'fdecl ast::Fdecl<'a>) -> Self {
        let mut g = Self {
            fdecl,
            label_to_bbix: fdecl.cfg.blocks.iter().enumerate().map(|(i, (lbl, _blk))| (*lbl, i + 1)).collect(),
            // to be initialized later
            facts: Default::default(),
            block_preds: vec![Vec::new(); fdecl.cfg.blocks.len() + 2],
        };

        for n in g.nodes() {
            g.facts.insert(n, Default::default());
        }

        g.add_block_as_pred(0, &fdecl.cfg.entry);
        for (ix, (_, b)) in fdecl.cfg.blocks.iter().enumerate() {
            g.add_block_as_pred(ix + 1, b);
        }

        g
    }

    fn add_block_as_pred(&mut self, bbix: usize, block: &ast::Block) {
        match block.term.1 {
            ast::Terminator::Ret(_, _) => {
                let len = self.block_preds.len();
                self.block_preds[len - 1].push(bbix);
            }
            ast::Terminator::Br(lbl) => {
                let pred = self.label_to_bbix[&lbl];
                self.block_preds[pred].push(bbix);
            }
            ast::Terminator::Cbr(_, lbl1, lbl2) => {
                let pred = self.label_to_bbix[&lbl1];
                self.block_preds[pred].push(bbix);
                let pred = self.label_to_bbix[&lbl2];
                self.block_preds[pred].push(bbix);
            }
        }
    }
}

impl<'a, F> Graph<'a, '_, F> {
    fn nodes_before(&self, n: Node) -> Vec<Node> {
        match n {
            Node::Insn { bbix, ix } => {
                if ix != 0 {
                    return vec![Node::Insn { bbix, ix: ix - 1 }];
                }
                
                self.block_preds[bbix]
                    .iter()
                    .map(|&bbix| Node::Term { bbix })
                    .collect()
            }
            Node::Term { bbix } => {
                let insn_count = if bbix == 0 {
                    self.fdecl.cfg.entry.insns.len()
                } else {
                    self.fdecl.cfg.blocks[bbix-1].1.insns.len()
                };

                if insn_count > 0 {
                    return vec![Node::Insn { bbix, ix: insn_count - 1 }];
                }

                self.block_preds[bbix]
                    .iter()
                    .map(|&bbix| Node::Term { bbix })
                    .collect()
            }
            // the boundary node is always at the end of the cfg
            Node::Boundary => {
                self.block_preds[self.block_preds.len() - 1]
                    .iter()
                    .map(|&bbix| Node::Term { bbix })
                    .collect()
            }
        }
    }

    fn nodes_after(&self, n: Node) -> Vec<Node> {
        match n {
            Node::Insn { bbix, ix } => {
                let insn_count = if bbix == 0 {
                    self.fdecl.cfg.entry.insns.len()
                } else {
                    self.fdecl.cfg.blocks[bbix-1].1.insns.len()
                };
                if ix != insn_count - 1 {
                    vec![Node::Insn { bbix, ix: ix + 1 }]
                } else {
                    vec![Node::Term { bbix }]
                }
                
            }
            Node::Term { bbix } => {
                let block = if bbix == 0 {
                    &self.fdecl.cfg.entry
                } else {
                    &self.fdecl.cfg.blocks[bbix-1].1
                };

                let following_blocks = match block.term.1 {
                    ast::Terminator::Ret(_, _) => return vec![Node::Boundary],
                    ast::Terminator::Br(lbl) => vec![lbl],
                    ast::Terminator::Cbr(_, lbl1, lbl2) => vec![lbl1, lbl2],
                };

                let nodes: Vec<_> = following_blocks.into_iter().map(|lbl| {
                    let bbix = self.label_to_bbix[&lbl];
                    let insn_count = if bbix == 0 {
                        self.fdecl.cfg.entry.insns.len()
                    } else {
                        self.fdecl.cfg.blocks[bbix-1].1.insns.len()
                    };

                    if insn_count == 0 {
                        Node::Term { bbix }
                    } else {
                        Node::Insn { bbix, ix: 0}
                    }
                })
                .collect();

                nodes
            }
            // the boundary node is always at the end of the cfg
            Node::Boundary => vec![],
        }
    }
}

impl<'a, F: DataflowFact<'a>> Graph<'a, '_, F> {
    fn into_analysis(mut self) -> Analysis<'a, F> {
        let mut blocks = vec![&self.fdecl.cfg.entry];
        blocks.extend(self.fdecl.cfg.blocks.iter().map(|(_lbl, b)| b));

        let mut nodes = Vec::new();
        let mut uids = Vec::new();
        
        if F::forward() {
            nodes.push(Node::Boundary);
        }

        for (bbix, block) in blocks.into_iter().enumerate() {
            for (ix, (uid, _insn)) in block.insns.iter().enumerate() {
                nodes.push(Node::Insn { bbix, ix });
                uids.push(*uid);
            }
            nodes.push(Node::Term { bbix });
            uids.push(block.term.0);
        }

        if !F::forward() {
            nodes.push(Node::Boundary);
        }

        Analysis {
            map: uids
                .into_iter()
                .enumerate()
                .map(|(ix, uid)| (uid, ix + 1))
                .collect(),
            vec: nodes
                .into_iter()
                .map(|node| self.facts.remove(&node).unwrap())
                .collect(),
        }
    }
}

impl<'a, F: DataflowFact<'a> + Clone> DFAGraph<'a> for Graph<'a, '_, F> {
    type Fact = F;

    type Node = Node;

    fn out(&self, n: &Self::Node) -> Self::Fact {
        self.facts[n].clone()
    }

    fn preds(&self, n: &Self::Node) -> Vec<Self::Node> {
        if F::forward() {
            self.nodes_before(*n)
        } else {
            self.nodes_after(*n)
        }
    }

    fn succs(&self, n: &Self::Node) -> Vec<Self::Node> {
        if F::forward() {
            self.nodes_after(*n)
        } else {
            self.nodes_before(*n)
        }
    }

    fn nodes(&self) -> Vec<Self::Node> {
        fn add(block: &ast::Block<'_>, bbix: usize, nodes: &mut Vec<Node>) {
            for (ix, _) in block.insns.iter().enumerate() {
                nodes.push(Node::Insn {
                    bbix,
                    ix,
                });
            }
            nodes.push(Node::Term { bbix });
        }

        let mut nodes = vec![Node::Boundary];
        add(&self.fdecl.cfg.entry, 0, &mut nodes);
        for (bbix, (_lbl, bb)) in self.fdecl.cfg.blocks.iter().enumerate() {
            add(bb, bbix + 1, &mut nodes);
        }
        nodes
    }

    fn flow(&self, n: &Self::Node, inn: Self::Fact) -> Self::Fact  {
        match *n {
            Node::Insn { bbix, ix } => {
                let block = if bbix == 0 {
                    &self.fdecl.cfg.entry
                } else { 
                    &self.fdecl.cfg.blocks[bbix-1].1
                };
                let (def, insn) = &block.insns[ix];
                inn.instruction_flow(*def, insn)
            }
            Node::Term { bbix } => {
                let block = if bbix == 0 {
                    &self.fdecl.cfg.entry
                } else { 
                    &self.fdecl.cfg.blocks[bbix-1].1
                };
                inn.terminator_flow(&block.term.1)
            }
            // todo: is this right?
            Node::Boundary => inn,
        }
    }

    fn add_fact(&mut self, n: &Self::Node, f: Self::Fact) {
        self.facts.insert(*n, f);
    }
}
