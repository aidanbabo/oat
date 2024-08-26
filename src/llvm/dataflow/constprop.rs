use std::collections::HashMap;

use crate::llvm::ast;
use crate::llvm::dataflow::{DataflowFact, Graph, Analysis, solve};

pub fn run<'a>(fdecl: &ast::Fdecl<'a>) -> Analysis<'a, Fact<'a>> {
    let graph = Graph::<'_, '_, Fact>::from_fdecl(fdecl);
    solve(graph).into_analysis()
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Const {
    Yes(i64),
    No,
    Undef,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Fact<'a>(pub HashMap<ast::Uid<'a>, Const>);

impl<'a> Fact<'a> {
    fn constness_of_operand(&self, o: ast::Operand<'_>) -> Const {
        match o {
            ast::Operand::Null => Const::Undef,
            ast::Operand::Const(v) => Const::Yes(v),
            ast::Operand::Gid(_id) => Const::Undef, // todo: match UID line
            ast::Operand::Id(id) => self.0.get(&id).copied().unwrap_or(Const::Undef)
        }
    }
}

impl<'a> DataflowFact<'a> for Fact<'a> {
    fn combine(facts: &[Self]) -> Self {
        let mut map = HashMap::new();
        for fact in facts {
            for (uid, ainfo) in &fact.0 {
                let new = if let Some(existing) = map.get(uid) {
                    match (*existing, *ainfo) {
                        (Const::Yes(c1), Const::Yes(c2)) => {
                            // should be same c?
                            assert_eq!(c1, c2);
                            Const::Yes(c1)
                        }
                        (Const::Yes(c), _) | (_, Const::Yes(c)) => Const::Yes(c),
                        (Const::No, _) | (_, Const::No) => Const::No,
                        _ => Const::Undef,
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

    // todo: add arithmetic identities
    fn instruction_flow(mut self, uid: ast::Uid<'a>, insn: &ast::Insn<'a>) -> Self {
        match insn {
            ast::Insn::Binop(bop, _, o1, o2) => {
                let constness = match (self.constness_of_operand(*o1), self.constness_of_operand(*o2)) {
                    (Const::Yes(c1), Const::Yes(c2)) => Const::Yes(do_bop(*bop, c1, c2)),
                    (_, Const::No) | (Const::No, _) => Const::No,
                    (_, Const::Undef) | (Const::Undef, _) => Const::Undef,
                };
                self.0.insert(uid, constness);
            }
            ast::Insn::Icmp(cnd, _, o1, o2) => {
                let constness = match (self.constness_of_operand(*o1), self.constness_of_operand(*o2)) {
                    (Const::Yes(c1), Const::Yes(c2)) => Const::Yes(do_icmp(*cnd, c1, c2) as i64),
                    (_, Const::No) | (Const::No, _) => Const::No,
                    (_, Const::Undef) | (Const::Undef, _) => Const::Undef,
                };
                self.0.insert(uid, constness);
            }
            ast::Insn::Store(..) | ast::Insn::Call(ast::Ty::Void, _, _) => {
                self.0.insert(uid, Const::Undef);
            }
            _ => {
                self.0.insert(uid, Const::No);
            }
        }
        self
    }

    fn terminator_flow(self, _: &ast::Terminator<'a>) -> Self {
        self
    }
}

fn do_bop(bop: ast::Bop, a: i64, b: i64) -> i64 {
    match bop {
        ast::Bop::Add => a + b,
        ast::Bop::Sub => a - b,
        ast::Bop::Mul => a * b,
        ast::Bop::Shl => a << b,
        ast::Bop::Lshr => ((a as u64) >> (b as u64)) as i64,
        ast::Bop::Ashr => a >> b,
        ast::Bop::And => a & b,
        ast::Bop::Or => a | b,
        ast::Bop::Xor => a ^ b,
    }
}

fn do_icmp(cnd: ast::Cnd, a: i64, b: i64) -> bool {
    match cnd {
        ast::Cnd::Eq => a == b,
        ast::Cnd::Ne => a != b,
        ast::Cnd::Slt => a < b,
        ast::Cnd::Sle => a <= b,
        ast::Cnd::Sgt => a > b,
        ast::Cnd::Sge => a >= b,
    }
}

pub fn propagate(mut ll_prog: ast::Prog) -> ast::Prog {
    for (_name, fdecl) in &mut ll_prog.fdecls {
        let constness = run(fdecl);

        // todo: this pattern happens too often, make an iterator or smth
        constprop_block(&mut fdecl.cfg.entry, &constness);
        for (_, b) in &mut fdecl.cfg.blocks {
            constprop_block(b, &constness);
        }
    }

    ll_prog
}

fn constprop_block<'a>(b: &mut ast::Block<'a>, constness: &Analysis<Fact<'a>>) {
    for (uid, insn) in &mut b.insns {
        let fact = constness.out_at(*uid);
        match insn {
            ast::Insn::Binop(_, _, o1, o2) |
            ast::Insn::Icmp(_, _, o1, o2) |
            ast::Insn::Store(_, o1, o2) => {
                maybe_update_operand(o1, fact);
                maybe_update_operand(o2, fact);
            }
            ast::Insn::Bitcast(_, o, _) |
            ast::Insn::Load(_, o) => maybe_update_operand(o, fact),
            ast::Insn::Gep(_, o, os) => {
                maybe_update_operand(o, fact);
                for o in os {
                    maybe_update_operand(o, fact);
                }
            }
            ast::Insn::Call(_, o, os) => {
                maybe_update_operand(o, fact);
                for (_t, o) in os {
                    maybe_update_operand(o, fact);
                }
            }
            ast::Insn::Alloca(_) => {}
        }
    }

    let fact = constness.out_at(b.term.0);
    match &mut b.term.1 {
        ast::Terminator::Cbr(o, _, _) |
        ast::Terminator::Ret(_, Some(o)) => maybe_update_operand(o, fact),
        ast::Terminator::Ret(_, None) | ast::Terminator::Br(_) => {},
    }
}

fn maybe_update_operand(o: &mut ast::Operand<'_>, fact: &Fact<'_>) {
    if let ast::Operand::Id(id) = o {
        if let Some(Const::Yes(c)) = fact.0.get(id) {
            *o = ast::Operand::Const(*c);
        }
    }
}
