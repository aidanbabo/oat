use crate::llvm::ast;
use crate::llvm::dataflow::{Analysis, liveness, alias};

// todo: multiple rounds of dce until fixed point, will be slow but could maybe find a dataflow-way
// to only rerun on blocks that could benefit from it
pub fn run(mut ll_prog: ast::Prog) -> ast::Prog {
    for (_name, fdecl) in &mut ll_prog.fdecls {
        let liveness = liveness::run(fdecl);
        let alias = alias::run(fdecl);

        for b in fdecl.cfg.block_iter_mut() {
            dce_block(b, &liveness, &alias);
        }
    }

    ll_prog
}

fn dce_block<'a>(b: &mut ast::Block<'a>, liveness: &Analysis<liveness::Fact<'a>>, alias: &Analysis<alias::Fact<'a>>) {
    b.insns.retain(|(uid, insn)| {
        let keep = match insn {
            ast::Insn::Call(_, _, _) | ast::Insn::Store(_, _, ast::Operand::Gid(_)) => true,
            ast::Insn::Store(_, _, ast::Operand::Id(id)) => {
                let lives = liveness.out_at(*uid).0.contains(id);
                let unique = alias.out_at(*uid).0.get(id).copied().unwrap_or(alias::Alias::Undef) != alias::Alias::May;
                lives || !unique
            }
            _ => {
                liveness.out_at(*uid).0.contains(uid)
            }
        };
        keep
    });
}
