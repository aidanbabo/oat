use internment::Arena;
use std::collections::HashMap;

use crate::llvm::ast as ll;
use crate::backend::platform;
use super::ast::*;

type Layout<'ll> = HashMap<ll::Uid<'ll>, Op<'static>>;

struct FunctionContext<'ll, 'asm> {
    arena: &'asm Arena<str>,
    layout: Layout<'ll>,
    name: ll::Lbl<'ll>,
    tdecls: &'ll HashMap<ll::Uid<'ll>, ll::Ty<'ll>>,
}

pub fn x64_from_llvm<'asm>(ll: ll::Prog, arena: &'asm Arena<str>) -> Prog<'asm> {
    let mut p = Prog {
        code: Vec::new(),
        data: Vec::new(),
    };

    // assert!(ll.edecls.is_empty(), "no support for edecls");

    for (name, (_ty, ginit)) in ll.gdecls {
        let block = DataBlock {
            global: true,
            label: arena.intern_string(platform::mangle(&name)),
            data: compile_global(arena, ginit),
        };
        p.data.push(block);
    }

    for (name, fdecl) in ll.fdecls {
        let (arg_layout, stack_layout) = layout(&fdecl);

        let fctx = FunctionContext {
            arena,
            layout: stack_layout,
            name,
            tdecls: &ll.tdecls,
        };

        let code_blocks = compile_function(fctx, arg_layout, name, fdecl);
        p.code.extend(code_blocks);
    }
    p
}

fn compile_global<'asm>(arena: &'asm Arena<str>, ginit: ll::Ginit<'_>) -> Vec<Data<'asm>> {
    match ginit {
        ll::Ginit::Null => vec![Data::Quad(Imm::Word(0))],
        ll::Ginit::Gid(gid) => vec![Data::Quad(Imm::Lbl(arena.intern_string(platform::mangle(&gid))))],
        ll::Ginit::Int(i) => vec![Data::Quad(Imm::Word(i))],
        ll::Ginit::String(s) => vec![Data::String(s)],
        ll::Ginit::Array(gs) | ll::Ginit::Struct(gs) => gs.into_iter().flat_map(|(_, g)| compile_global(arena, g)).collect(),
        ll::Ginit::Bitcast(_, g, _) => compile_global(arena, *g),
    }
}

fn compile_function<'ll, 'asm>(fctx: FunctionContext<'ll, 'asm>, arg_layout: Vec<(ll::Uid<'ll>, Op<'asm>)>, name: ll::Gid<'ll>, fdecl: ll::Fdecl<'ll>) -> Vec<CodeBlock<'asm>> {
    let stack_size = fctx.layout.len();

    let mut b1 = CodeBlock {
        global: true,
        label: fctx.arena.intern_string(platform::mangle(&name)),
        insns: vec![
            Insn::Push(Op::Reg(Reg::Rbp)),
            Insn::Mov(Op::Reg(Reg::Rsp), Op::Reg(Reg::Rbp)),
            Insn::Sub(Op::Imm(Imm::Word(8 * stack_size as i64)), Op::Reg(Reg::Rsp)),
        ],
    };

    // move register args to their stack slots so they don't get clobbered
    b1.insns.extend(
        arg_layout
            .into_iter()
            .map(|(uid, loc)| {
                Insn::Mov(loc, fctx.layout[&uid])
            })
    );

    
    let mut blocks = Vec::new();
    let entry = compile_block(&fctx, b1, fdecl.cfg.entry);
    blocks.push(entry);

    for (lbl, b) in fdecl.cfg.blocks {
        blocks.push(compile_labelled_block(&fctx, lbl, b));
    }
    blocks
}

fn layout<'ll>(fdecl: &ll::Fdecl<'ll>) -> (Vec<(ll::Uid<'ll>, Op<'static>)>, Layout<'ll>) {
    let arg_layout = fdecl
        .params
        .iter()
        .copied()
        .take(6)
        .zip([
            Op::Reg(Reg::Rdi),
            Op::Reg(Reg::Rsi),
            Op::Reg(Reg::Rdx),
            Op::Reg(Reg::Rcx),
            Op::Reg(Reg::R8),
            Op::Reg(Reg::R9),
        ])
        .collect();


    fn arg_callee_loc(n: i64) -> Op<'static> {
        if n < 6 {
            Op::Ind3(Imm::Word(-8 * (n + 1)), Reg::Rbp)
        } else {
            Op::Ind3(Imm::Word(8 * (n - 4)), Reg::Rbp)
        }
    }

    let mut layout = HashMap::new();
    for (i, uid) in fdecl.params.iter().enumerate() {
        layout.insert(*uid, arg_callee_loc(i as i64));
    }

    fn find_all_uids<'ll>(uids: &mut Vec<ll::Uid<'ll>>, b: &ll::Block<'ll>) {
        for (uid, _) in &b.insns {
            // todo: this is a hack! more sophisticated filtering please!
            if !uid.starts_with('_') {
                uids.push(*uid);
            }
        }
    }
    let mut body_uids = Vec::new();
    find_all_uids(&mut body_uids, &fdecl.cfg.entry);
    for (_, b) in &fdecl.cfg.blocks {
        find_all_uids(&mut body_uids, b);
    }
    // why?
    body_uids.reverse();

    let local_offset = std::cmp::min(7, fdecl.params.len() + 1) as i64;
    let ind3 = |i: i64| Op::Ind3(Imm::Word(-8 * (i + local_offset)), Reg::Rbp);
    layout.extend(body_uids.into_iter()
        .enumerate()
        .map(|(i, uid)| (uid, ind3(i as i64)))
    );

    (arg_layout, layout)
}

fn compile_labelled_block<'ll, 'asm>(fctx: &FunctionContext<'ll, 'asm>, label: ll::Uid<'ll>, block: ll::Block<'ll>) -> CodeBlock<'asm> {
    let b = CodeBlock {
        global: false,
        label: mk_lbl(fctx, label),
        insns: Vec::new(),
    };
    compile_block(fctx, b, block)
}

fn compile_block<'ll, 'asm>(fctx: &FunctionContext<'ll, 'asm>, mut asm: CodeBlock<'asm>, ll: ll::Block<'ll>) -> CodeBlock<'asm> {
    for (uid, insn) in ll.insns {
        compile_insn(fctx, &mut asm, uid, insn);
    }
    compile_terminator(fctx, asm, ll.term.1)
}

fn compile_insn<'ll, 'asm>(fctx: &FunctionContext<'ll, 'asm>, asm: &mut CodeBlock<'asm>, uid: ll::Uid<'ll>, insn: ll::Insn<'ll>) {
    match insn {
        ll::Insn::Binop(bop, _, lhs, rhs) => {
            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rax), lhs));
            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rcx), rhs));
            let bop = match bop {
                ll::Bop::Add => Insn::Add(Op::Reg(Reg::Rcx), Op::Reg(Reg::Rax)),
                ll::Bop::Sub => Insn::Sub(Op::Reg(Reg::Rcx), Op::Reg(Reg::Rax)),
                ll::Bop::Mul => Insn::Imul(Op::Reg(Reg::Rcx), Reg::Rax),
                ll::Bop::Shl => Insn::Shl(Op::Reg(Reg::Rcx), Op::Reg(Reg::Rax)),
                ll::Bop::Lshr => Insn::Shr(Op::Reg(Reg::Rcx), Op::Reg(Reg::Rax)),
                ll::Bop::Ashr => Insn::Sar(Op::Reg(Reg::Rcx), Op::Reg(Reg::Rax)),
                ll::Bop::And => Insn::And(Op::Reg(Reg::Rcx), Op::Reg(Reg::Rax)),
                ll::Bop::Or => Insn::Or(Op::Reg(Reg::Rcx), Op::Reg(Reg::Rax)),
                ll::Bop::Xor => Insn::Xor(Op::Reg(Reg::Rcx), Op::Reg(Reg::Rax)),
            };
            asm.insns.push(bop);
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), fctx.layout[&uid]));
        }
        ll::Insn::Alloca(_) => {
            asm.insns.push(Insn::Push(Op::Imm(Imm::Word(0))));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rsp), fctx.layout[&uid]));
        }
        ll::Insn::Load(_, op) => {
            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rax), op));
            asm.insns.push(Insn::Mov(Op::Ind2(Reg::Rax), Op::Reg(Reg::Rax)));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), fctx.layout[&uid]));
        }
        ll::Insn::Store(_, src, dst) => {
            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rax), src));
            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rcx), dst));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), Op::Ind2(Reg::Rcx)));
        }
        ll::Insn::Icmp(cnd, _, lhs, rhs) => {
            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rdi), lhs));
            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rsi), rhs));
            asm.insns.push(Insn::Xor(Op::Reg(Reg::Rax), Op::Reg(Reg::Rax)));
            asm.insns.push(Insn::Cmp(Op::Reg(Reg::Rsi), Op::Reg(Reg::Rdi)));
            asm.insns.push(Insn::Set(compile_cnd(cnd), Op::Reg(Reg::Rax)));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), fctx.layout[&uid]));
        }
        ll::Insn::Call(ret_ty, fname, args) => {
            for (i, (_, arg)) in args.into_iter().enumerate().rev() {
                let insn = match i {
                    0 => compile_operand(fctx, Op::Reg(Reg::Rdi), arg),
                    1 => compile_operand(fctx, Op::Reg(Reg::Rsi), arg),
                    2 => compile_operand(fctx, Op::Reg(Reg::Rdx), arg),
                    3 => compile_operand(fctx, Op::Reg(Reg::Rcx), arg),
                    4 => compile_operand(fctx, Op::Reg(Reg::R8), arg),
                    5 => compile_operand(fctx, Op::Reg(Reg::R9), arg),
                    _ => Insn::Push(translate_op(fctx, arg)),
                };
                asm.insns.push(insn);
            }

            match fname {
                ll::Operand::Gid(lbl) => {
                    // fastpath
                    asm.insns.push(Insn::Call(Op::Imm(Imm::Lbl(fctx.arena.intern_string(platform::mangle(&lbl))))));
                }
                _ => {
                    asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rax), fname));
                    asm.insns.push(Insn::Call(Op::Reg(Reg::Rax)));
                }
            }

            if ret_ty != ll::Ty::Void {
                asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), fctx.layout[&uid]));
            }
        }
        ll::Insn::Bitcast(_, o, _) => {
            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rax), o));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), fctx.layout[&uid]));
        }
        ll::Insn::Gep(t, op, path) => {
            fn size_ty<'ll, 'asm>(fctx: &FunctionContext<'ll, 'asm>, ty: &ll::Ty) -> i64 {
                match ty {
                    ll::Ty::Void | ll::Ty::I8 | ll::Ty::Fun(..) => panic!("undefined size, what the hell"),
                    ll::Ty::I1 | ll::Ty::I64 | ll::Ty::Ptr(..) => 8,
                    ll::Ty::Struct(ts) => ts.iter().map(|t| size_ty(fctx, t)).sum(),
                    ll::Ty::Array(n, t) => n * size_ty(fctx, t),
                    ll::Ty::Named(name) => size_ty(fctx, &fctx.tdecls[&name]),
                }
            }

            fn index_into<'ll, 'asm>(fctx: &FunctionContext<'ll, 'asm>, ts: &[ll::Ty<'ll>], n: i64) -> i64 {
                ts
                    .iter()
                    .take(n as usize)
                    .map(|t| size_ty(fctx, t))
                    .sum()
            }

            fn path_through<'ll, 'asm>(asm: &mut CodeBlock<'asm>, fctx: &FunctionContext<'ll, 'asm>, curr_ty: ll::Ty<'ll>, p: ll::Operand<'ll>) -> ll::Ty<'ll> {
                match curr_ty {
                    ll::Ty::Struct(mut ts) => {
                            let ll::Operand::Const(n) = p else { panic!("non-const op for struct index") };
                            let offset = index_into(fctx, &ts, n);
                            asm.insns.push(Insn::Add(Op::Imm(Imm::Word(offset)), Op::Reg(Reg::Rax)));
                            // todo: gross? i can't just use indexing
                            ts.swap_remove(n as usize)
                    }
                    ll::Ty::Array(_, new_ty) => {
                        if let ll::Operand::Const(ix) = p {
                            let offset = size_ty(fctx, &new_ty) * ix;
                            asm.insns.push(Insn::Add(Op::Imm(Imm::Word(offset)), Op::Reg(Reg::Rax)));
                            *new_ty
                        } else {
                            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), Op::Reg(Reg::Rcx)));
                            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rax), p));
                            asm.insns.push(Insn::Imul(Op::Imm(Imm::Word(size_ty(fctx, &new_ty))), Reg::Rax));
                            asm.insns.push(Insn::Add(Op::Reg(Reg::Rcx), Op::Reg(Reg::Rax)));
                            *new_ty
                        }
                    }
                    ll::Ty::Named(name) => path_through(asm, fctx, fctx.tdecls[&name].clone(), p),
                    _ => unreachable!("bad gep op"),
                }
            }

            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rax), op));
            path
                .into_iter()
                .fold(ll::Ty::Array(0, Box::new(t)), |ty, p| path_through(asm, fctx, ty, p));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), fctx.layout[&uid]));
        }
    }
}

fn compile_terminator<'ll, 'asm>(fctx: &FunctionContext<'ll, 'asm>, mut asm: CodeBlock<'asm>, term: ll::Terminator<'ll>) -> CodeBlock<'asm> {
    match term {
        ll::Terminator::Ret(_ty, var) => {
            if let Some(var) = var {
                asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rax), var));
            }
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rbp), Op::Reg(Reg::Rsp)));
            asm.insns.push(Insn::Pop(Op::Reg(Reg::Rbp)));
            asm.insns.push(Insn::Ret);
        }
        ll::Terminator::Br(lbl) => {
            asm.insns.push(Insn::Jmp(Op::Imm(Imm::Lbl(mk_lbl(fctx, lbl)))));
        }
        ll::Terminator::Cbr(op, true_lbl, false_lbl) => {
            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rax), op));
            asm.insns.push(Insn::Cmp(Op::Imm(Imm::Word(0)), Op::Reg(Reg::Rax)));
            asm.insns.push(Insn::J(Cond::Eq, Op::Imm(Imm::Lbl(mk_lbl(fctx, false_lbl)))));
            asm.insns.push(Insn::Jmp(Op::Imm(Imm::Lbl(mk_lbl(fctx, true_lbl)))));
        }
    }

    asm
}

fn compile_cnd(cnd: ll::Cnd) -> Cond {
    match cnd {
        ll::Cnd::Eq => Cond::Eq,
        ll::Cnd::Ne => Cond::Neq,
        ll::Cnd::Slt => Cond::Lt,
        ll::Cnd::Sle => Cond::Le,
        ll::Cnd::Sgt => Cond::Gt,
        ll::Cnd::Sge => Cond::Ge,
    }
}

fn mk_lbl<'ll, 'asm>(fctx: &FunctionContext<'ll, 'asm>, lbl: ll::Lbl<'ll>) -> Label<'asm> {
    fctx.arena.intern_string(format!("{}.{}", fctx.name, lbl))
}

fn compile_operand<'ll, 'asm>(fctx: &FunctionContext<'ll, 'asm>, dst: Op<'asm>, src: ll::Operand<'ll>) -> Insn<'asm> {
    match src {
        ll::Operand::Gid(_) => Insn::Lea(translate_op(fctx, src), dst),
        _ => Insn::Mov(translate_op(fctx, src), dst),
    }
}

fn translate_op<'ll, 'asm>(fctx: &FunctionContext<'ll, 'asm>, op: ll::Operand<'ll>) -> Op<'asm> {
    match op {
        ll::Operand::Null => Op::Imm(Imm::Word(0)),
        ll::Operand::Const(c) => Op::Imm(Imm::Word(c)),
        // todo: mangle?
        ll::Operand::Gid(gid) => Op::Ind3(Imm::Lbl(fctx.arena.intern_string(platform::mangle(&gid))), Reg::Rip),
        ll::Operand::Id(uid) => fctx.layout[&uid],
    }
}
