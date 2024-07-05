// the reference implementation is rather complicated
// it uses lots of functors to allow both the solver and api consumer to write as little code as
// possible
// replicating this structure in rust code is looking to be cumbersome, so the api consumer will
// take on a portion of the work, if we can find a way to reduce duplication on that side, it may
// be smart
// the reference implementation also creates a dfagraph which operates on whole basic blocks at
// once to speed things up, this is an optimization that we most definitely want, but we also just
// want any working code to start

// todo: priv the whole thing
pub mod liveness;

pub trait DataflowFact : std::cmp::PartialEq + std::fmt::Debug {
    fn combine(facts: &[Self]) -> Self where Self: Sized;
}

pub trait DFAGraph {
    type Fact : DataflowFact;
    type Node;

    /// Gets the fact flowing out of a node
    fn out(&self, n: &Self::Node) -> Self::Fact;

    /// Gets the predecessors or successors of a node
    fn preds(&self, n: &Self::Node) -> Vec<Self::Node>;
    fn succs(&self, n: &Self::Node) -> Vec<Self::Node>;
    /// Gets all nodes
    fn nodes(&self) -> Vec<Self::Node>;

    /// Gets the result of flowing a certain fact through a node
    /// pairs well with add_fact
    fn flow(&self, n: &Self::Node, inn: &Self::Fact) -> Self::Fact ;
    /// Sets the fact flowing out of a node
    fn add_fact(&mut self, n: &Self::Node, f: Self::Fact);
}

pub fn solve<T>(mut graph: T) -> T
    where T: DFAGraph
{
    // todo: remove duplicates in worklist
    let mut worklist = graph.nodes();
    while let Some(node) = worklist.pop() {
        let old_out = graph.out(&node);
        let old_facts: Vec<_> = graph.preds(&node).into_iter().map(|n| graph.out(&n)).collect();
        let inn = DataflowFact::combine(&old_facts);
        let new_out = graph.flow(&node, &inn);
        let change = old_out != new_out;
        graph.add_fact(&node, new_out);
        if change {
            worklist.extend(graph.succs(&node));
        }
    }
    graph
}
