use std::collections::HashSet;

use crate::llvm::ast;
use crate::llvm::dataflow::{DataflowFact, Graph, Analysis, solve};

pub fn run<'a>(fdecl: &ast::Fdecl<'a>) -> Analysis<'a, Fact<'a>> {
    let graph = Graph::<'_, '_, Fact>::from_fdecl(fdecl);
    solve(graph).into_analysis()
}

// todo: bitvector
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Fact<'a>(pub HashSet<ast::Uid<'a>>);

fn fact_from_def_use<'a>(old_in: Fact<'a>, def: Option<ast::Uid<'a>>, uze: &[ast::Operand<'a>]) -> Fact<'a> {
        let mut new_in = old_in.0;
        if let Some(d) = def {
            new_in.remove(&d);
        }
        new_in.extend(
            uze
            .iter()
            .filter_map(|o| if let ast::Operand::Id(id) = o { Some(id)} else { None })
        );
        Fact(new_in)
}

impl<'a> DataflowFact<'a> for Fact<'a> {
    fn combine(facts: &[Self]) -> Self where Self: Sized {
        facts.iter().fold(Fact(HashSet::new()), |acc, fact| Fact(acc.0.union(&fact.0).copied().collect()))
    }

    fn forward() -> bool { false }

    fn instruction_flow(self, uid: ast::Uid<'a>, insn: &ast::Insn<'a>) -> Self {
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

        fact_from_def_use(self, Some(uid), &ops)
    }

    fn terminator_flow(self, term: &ast::Terminator<'a>) -> Self {
        let ops = match term {
            ast::Terminator::Ret(_, Some(o)) |
            ast::Terminator::Cbr(o, _, _) => vec![*o],
            ast::Terminator::Ret(_, None) |
            ast::Terminator::Br(_) => vec![],
        };
        fact_from_def_use(self, None, &ops)
    }
}
