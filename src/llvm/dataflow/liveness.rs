use crate::llvm::ast::{self, Fdecl, Uid};
use crate::llvm::dataflow::{DataflowFact, DFAGraph};
use std::collections::{HashSet, HashMap};

#[derive(Clone, Debug, PartialEq)]
pub struct Fact<'a>(HashSet<Uid<'a>>);

impl DataflowFact for Fact<'_> {
    fn combine(facts: &[Self]) -> Self where Self: Sized {
        facts.iter().fold(Fact(HashSet::new()), |acc, fact| Fact(acc.0.union(&fact.0).copied().collect()))
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Node {
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
    /// special boundary node representing the edge entering at the top (the last instructions
    /// cause liveness is backwards)
    Boundary,
}

#[derive(Debug)]
pub struct Graph<'a> {
    fdecl: &'a Fdecl<'a>,
    /// map bbix -> [bbix], has a space at the end for the boundary block and at the start for the
    /// entry block
    pub block_preds: Vec<Vec<usize>>,
    label_to_bbix: HashMap<ast::Lbl<'a>, usize>,
    pub facts: HashMap<Node, Fact<'a>>,
}

impl<'a> Graph<'a> {
    pub fn from_fdecl(fdecl: &'a Fdecl<'a>) -> Self {
        let mut g = Self {
            fdecl,
            label_to_bbix: fdecl.cfg.blocks.iter().enumerate().map(|(i, (lbl, _blk))| (*lbl, i + 1)).collect(),
            // to be initialized later
            facts: Default::default(),
            block_preds: vec![Vec::new(); fdecl.cfg.blocks.len() + 2],
        };

        for n in g.nodes() {
            g.facts.insert(n, Fact(HashSet::new()));
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

impl<'a> DFAGraph for Graph<'a> {
    type Fact = Fact<'a>;

    type Node = Node;

    fn out(&self, n: &Self::Node) -> Self::Fact {
        self.facts[n].clone()
    }

    // this is a backwards analysis, so these are the nodes following `n`
    fn preds(&self, n: &Self::Node) -> Vec<Self::Node> {
        match *n {
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
            // this node is at the end because we are doing backwards analysis, no predecessor
            Node::Boundary => vec![],
        }
    }

    // this is a backwards analysis, so these are the nodes before `n`
    fn succs(&self, n: &Self::Node) -> Vec<Self::Node> {
        match *n {
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
            // this node is at the end because we are doing backwards analysis, so any block that
            // returns is it's successor
            Node::Boundary => {
                self.block_preds[self.block_preds.len() - 1]
                    .iter()
                    .map(|&bbix| Node::Term { bbix })
                    .collect()
            }
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

    fn flow(&self, n: &Self::Node, inn: &Self::Fact) -> Self::Fact  {
        let (def, uze) = match *n {
            Node::Insn { bbix, ix } => {
                let block = if bbix == 0 {
                    &self.fdecl.cfg.entry
                } else { 
                    &self.fdecl.cfg.blocks[bbix-1].1
                };
                let (def, insn) = &block.insns[ix];
                let ops = match insn {
                    ast::Insn::Alloca(_) => vec![],
                    ast::Insn::Bitcast(_, o, _) |
                    ast::Insn::Load(_, o) => vec![*o],
                    ast::Insn::Store(_, o1, o2) |
                    ast::Insn::Icmp(_, _, o1, o2) |
                    ast::Insn::Binop(_, _, o1, o2) => vec![*o1, *o2],
                    ast::Insn::Call(_, o, tos) => {
                        let mut os = vec![*o];
                        os.extend(tos.iter().map(|(_t, o)| *o));
                        os
                    }
                    ast::Insn::Gep(_, o, os) => {
                        let mut os = os.clone();
                        os.push(*o);
                        os
                    }
                };
                let uze: Vec<_> = ops.into_iter().filter_map(|o| if let ast::Operand::Id(id) = o { Some(id)} else { None }).collect();
                (Some(def), uze)
            }
            Node::Term { bbix } => {
                let block = if bbix == 0 {
                    &self.fdecl.cfg.entry
                } else { 
                    &self.fdecl.cfg.blocks[bbix-1].1
                };
                let ops = match block.term.1 {
                    ast::Terminator::Ret(_, Some(o)) |
                    ast::Terminator::Cbr(o, _, _) => vec![o],
                    ast::Terminator::Ret(_, None) |
                    ast::Terminator::Br(_) => vec![],
                };
                let uze: Vec<_> = ops.into_iter().filter_map(|o| if let ast::Operand::Id(id) = o { Some(id)} else { None }).collect();
                (None, uze)
            }
            // todo: is this right?
            Node::Boundary => (None, vec![]),
        };

        let mut new_in = inn.0.clone();
        if let Some(d) = def {
            new_in.remove(d);
        }
        new_in.extend(uze);
        Fact(new_in)
    }

    fn add_fact(&mut self, n: &Self::Node, f: Self::Fact) {
        self.facts.insert(*n, f);
    }
}
