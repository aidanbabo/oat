use std::collections::HashMap;

use crate::llvm::ast;
use crate::llvm::dataflow::DataflowFact;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Alias {
    No,
    May,
    Undef,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Fact<'a>(pub HashMap<ast::Uid<'a>, Alias>);

impl<'a> DataflowFact<'a> for Fact<'a> {
    fn combine(facts: &[Self]) -> Self {
        let mut map = HashMap::new();
        for fact in facts {
            for (uid, ainfo) in &fact.0 {
                let new = if let Some(existing) = map.get(uid) {
                    match (existing, ainfo) {
                        (Alias::May, _) | (_, Alias::May) => Alias::May,
                        (Alias::No, _) | (_, Alias::No) => Alias::No,
                        _ => Alias::Undef,
                    }
                } else {
                    *ainfo
                };
                map.insert(*uid, new);
            }
        }
        Fact(map)
    }

    fn forward() -> bool { true }

    fn instruction_flow(mut self, uid: ast::Uid<'a>, insn: &ast::Insn<'a>) -> Self {
        // for defined uid
        match insn {
            ast::Insn::Alloca(_) => {
                self.0.insert(uid, Alias::No);
            },
            ast::Insn::Load(ast::Ty::Ptr(..), _) |
            ast::Insn::Bitcast(_, _, ast::Ty::Ptr(..)) |
            ast::Insn::Gep(_, _, _) |
            ast::Insn::Call(ast::Ty::Ptr(..), _, _) => {
                self.0.insert(uid, Alias::May);
            }
            _ => {}
        }
        // for used uids
        match insn {
            ast::Insn::Store(ast::Ty::Ptr(..), ast::Operand::Id(id), _) |
            ast::Insn::Bitcast(ast::Ty::Ptr(..), ast::Operand::Id(id), _) |
            ast::Insn::Gep(_, ast::Operand::Id(id), _) => {
                self.0.insert(*id, Alias::May);
            }
            ast::Insn::Call(_, _, args) => {
                for (ty, op) in args {
                    // todo: no idea why Gids are included in here, try and remove?
                    if let (ast::Ty::Ptr(..), ast::Operand::Id(id) | ast::Operand::Gid(id)) = (ty, op) {
                        self.0.insert(*id, Alias::May);
                    }
                }
            }
            _ => {}
        }
        self
    }

    fn terminator_flow(self, _: &ast::Terminator<'a>) -> Self {
        self
    }
}
