use std::collections::HashMap;

use crate::StrInterner;
use crate::llvm::ast as ll;
use crate::backend::platform;
use super::ast::*;

type Layout<'ll> = HashMap<ll::Uid<'ll>, Op>;

struct FunctionContext<'ll> {
    layout: Layout<'ll>,
    name: ll::Gid<'ll>,
    tdecls: &'ll HashMap<ll::Tid, ll::Ty>,
    labels: &'ll Vec<Box<str>>,
}

pub fn x64_from_llvm(ll: ll::Prog<'_>) -> Prog {
    let mut p = Prog {
        code: Vec::new(),
        data: Vec::new(),
        labels: Vec::new(),
    };
    let mut labels = StrInterner::<Label>::default();
    // assert!(ll.edecls.is_empty(), "no support for edecls");

    for (name, (_ty, ginit)) in ll.gdecls {
        let block = DataBlock {
            global: true,
            label: make_global_label(&mut labels, &name),
            data: compile_global(&mut labels, ginit),
        };
        p.data.push(block);
    }

    for (name, fdecl) in ll.fdecls {
        let (arg_layout, stack_layout) = layout(&fdecl);

        let fctx = FunctionContext {
            layout: stack_layout,
            name,
            tdecls: &ll.tdecls,
            labels: &ll.tables.labels,
        };

        let code_blocks = compile_function(fctx, arg_layout, &mut labels, fdecl);
        p.code.extend(code_blocks);
    }
    p.labels = labels.pool;
    p
}

fn make_global_label(labels: &mut StrInterner<Label>, s: &str) -> Label {
    make_label(labels, s, true)
}

fn make_local_label(labels: &mut StrInterner<Label>, fctx: &FunctionContext<'_>, label_ix: ll::Lbl) -> Label {
    let s = format!("{}.{}", &fctx.name, &fctx.labels[label_ix.ix()]);
    make_label(labels, &s, false)
}

fn make_label(labels: &mut StrInterner<Label>, s: &str, mangle: bool) -> Label {
    let label = if mangle { 
        platform::mangle(s)
    } else {
        s.to_string()
    };
    labels.intern_string(label)
}

fn compile_global(labels: &mut StrInterner<Label>, ginit: ll::Ginit<'_>) -> Vec<Data> {
    match ginit {
        ll::Ginit::Null => vec![Data::Quad(Imm::Word(0))],
        ll::Ginit::Gid(gid) => vec![Data::Quad(Imm::Lbl(make_global_label(labels, &gid)))],
        ll::Ginit::Int(i) => vec![Data::Quad(Imm::Word(i))],
        ll::Ginit::String(s) => vec![Data::String(s)],
        ll::Ginit::Array(gs) | ll::Ginit::Struct(gs) => gs.into_iter().flat_map(|(_, g)| compile_global(labels, g)).collect(),
        ll::Ginit::Bitcast(_, g, _) => compile_global(labels, *g),
    }
}

fn compile_function<'ll>(fctx: FunctionContext<'ll>, arg_layout: Vec<(ll::Uid<'ll>, Op)>, labels: &mut StrInterner<Label>, fdecl: ll::Fdecl<'ll>) -> Vec<CodeBlock> {
    let stack_size = fctx.layout.len();

    let mut b1 = CodeBlock {
        global: true,
        label: make_global_label(labels, &fctx.name),
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
    let entry = compile_block(&fctx, labels, b1, fdecl.cfg.entry);
    blocks.push(entry);

    for (lbl, b) in fdecl.cfg.blocks {
        blocks.push(compile_labelled_block(&fctx, labels, lbl, b));
    }
    blocks
}

fn layout<'ll>(fdecl: &ll::Fdecl<'ll>) -> (Vec<(ll::Uid<'ll>, Op)>, Layout<'ll>) {
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


    fn arg_callee_loc(n: i64) -> Op {
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
        for (uid, insn) in &b.insns {
            if !matches!(insn, ll::Insn::Store(..)) {
                uids.push(*uid);
            }
        }
    }
    let mut body_uids = Vec::new();
    find_all_uids(&mut body_uids, &fdecl.cfg.entry);
    for (_, b) in &fdecl.cfg.blocks {
        find_all_uids(&mut body_uids, b);
    }

    let local_offset = std::cmp::min(7, fdecl.params.len() + 1) as i64;
    let ind3 = |i: i64| Op::Ind3(Imm::Word(-8 * (i + local_offset)), Reg::Rbp);
    layout.extend(body_uids.into_iter()
        .enumerate()
        .map(|(i, uid)| (uid, ind3(i as i64)))
    );

    (arg_layout, layout)
}

fn compile_labelled_block<'ll>(fctx: &FunctionContext<'ll>, labels: &mut StrInterner<Label>, label_ix: ll::Lbl, block: ll::Block<'ll>) -> CodeBlock {
    let b = CodeBlock {
        global: false,
        label: make_local_label(labels, fctx, label_ix),
        insns: Vec::new(),
    };
    compile_block(fctx, labels, b, block)
}

fn compile_block<'ll>(fctx: &FunctionContext<'ll>, labels: &mut StrInterner<Label>, mut asm: CodeBlock, ll: ll::Block<'ll>) -> CodeBlock {
    for (uid, insn) in ll.insns {
        compile_insn(fctx, labels, &mut asm, uid, insn);
    }
    compile_terminator(fctx, labels, asm, ll.term.1)
}

fn compile_insn<'ll>(fctx: &FunctionContext<'ll>, labels: &mut StrInterner<Label>, asm: &mut CodeBlock, uid: ll::Uid<'ll>, insn: ll::Insn<'ll>) {
    match insn {
        ll::Insn::Binop(bop, _, lhs, rhs) => {
            asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rax), lhs));
            asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rcx), rhs));
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
            asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rax), op));
            asm.insns.push(Insn::Mov(Op::Ind2(Reg::Rax), Op::Reg(Reg::Rax)));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), fctx.layout[&uid]));
        }
        ll::Insn::Store(_, src, dst) => {
            asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rax), src));
            asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rcx), dst));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), Op::Ind2(Reg::Rcx)));
        }
        ll::Insn::Icmp(cnd, _, lhs, rhs) => {
            asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rdi), lhs));
            asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rsi), rhs));
            asm.insns.push(Insn::Xor(Op::Reg(Reg::Rax), Op::Reg(Reg::Rax)));
            asm.insns.push(Insn::Cmp(Op::Reg(Reg::Rsi), Op::Reg(Reg::Rdi)));
            asm.insns.push(Insn::Set(compile_cnd(cnd), Op::Reg(Reg::Rax)));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), fctx.layout[&uid]));
        }
        ll::Insn::Call(ret_ty, fname, args) => {
            for (i, (_, arg)) in args.into_iter().enumerate().rev() {
                let insn = match i {
                    0 => compile_operand(fctx, labels, Op::Reg(Reg::Rdi), arg),
                    1 => compile_operand(fctx, labels, Op::Reg(Reg::Rsi), arg),
                    2 => compile_operand(fctx, labels, Op::Reg(Reg::Rdx), arg),
                    3 => compile_operand(fctx, labels, Op::Reg(Reg::Rcx), arg),
                    4 => compile_operand(fctx, labels, Op::Reg(Reg::R8), arg),
                    5 => compile_operand(fctx, labels, Op::Reg(Reg::R9), arg),
                    _ => Insn::Push(translate_op(fctx, labels, arg)),
                };
                asm.insns.push(insn);
            }

            match fname {
                ll::Operand::Gid(lbl) => {
                    // fastpath
                    asm.insns.push(Insn::Call(Op::Imm(Imm::Lbl(make_global_label(labels, &lbl)))));
                }
                _ => {
                    asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rax), fname));
                    asm.insns.push(Insn::Call(Op::Reg(Reg::Rax)));
                }
            }

            if ret_ty != ll::Ty::Void {
                asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), fctx.layout[&uid]));
            }
        }
        ll::Insn::Bitcast(_, o, _) => {
            asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rax), o));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), fctx.layout[&uid]));
        }
        ll::Insn::Gep(t, op, path) => {
            /// this is the size as determined by llvmlite, so it's a little nonsensical
            /// this also means we are abi incompatible with code compiled via the --clang option,
            /// which is fine ig
            fn size_ty(fctx: &FunctionContext<'_>, ty: &ll::Ty) -> i64 {
                match ty {
                    ll::Ty::Void | ll::Ty::Fun(..) => panic!("undefined size, what the hell"),
                    ll::Ty::I8 => 1, // this should only ever happen in compiling ll files
                    ll::Ty::I1 | ll::Ty::I64 | ll::Ty::Ptr(..) => 8,
                    ll::Ty::Struct(ts) => ts.iter().map(|t| size_ty(fctx, t)).sum(),
                    ll::Ty::Array(n, t) => n * size_ty(fctx, t),
                    ll::Ty::Named(name) => size_ty(fctx, &fctx.tdecls[name]),
                }
            }

            fn index_into(fctx: &FunctionContext<'_>, ts: &[ll::Ty], n: i64) -> i64 {
                ts
                    .iter()
                    .take(n as usize)
                    .map(|t| size_ty(fctx, t))
                    .sum()
            }

            fn path_through<'ll>(asm: &mut CodeBlock, fctx: &FunctionContext<'ll>, labels: &mut StrInterner<Label>, curr_ty: ll::Ty, p: ll::Operand<'ll>) -> ll::Ty {
                match curr_ty {
                    ll::Ty::Struct(mut ts) => {
                            let ll::Operand::Const(n) = p else { panic!("non-const op for struct index") };
                            let offset = index_into(fctx, &ts, n);
                            if offset != 0 {
                                asm.insns.push(Insn::Add(Op::Imm(Imm::Word(offset)), Op::Reg(Reg::Rax)));
                            }
                            // gross? i can't just use indexing
                            ts.swap_remove(n as usize)
                    }
                    ll::Ty::Array(_, new_ty) => {
                        if let ll::Operand::Const(ix) = p {
                            let offset = size_ty(fctx, &new_ty) * ix;
                            if offset != 0 {
                                asm.insns.push(Insn::Add(Op::Imm(Imm::Word(offset)), Op::Reg(Reg::Rax)));
                            }
                            *new_ty
                        } else {
                            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), Op::Reg(Reg::Rcx)));
                            asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rax), p));
                            asm.insns.push(Insn::Imul(Op::Imm(Imm::Word(size_ty(fctx, &new_ty))), Reg::Rax));
                            asm.insns.push(Insn::Add(Op::Reg(Reg::Rcx), Op::Reg(Reg::Rax)));
                            *new_ty
                        }
                    }
                    ll::Ty::Named(name) => path_through(asm, fctx, labels, fctx.tdecls[&name].clone(), p),
                    _ => unreachable!("bad gep op"),
                }
            }

            asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rax), op));
            path
                .into_iter()
                .fold(ll::Ty::Array(0, Box::new(t)), |ty, p| path_through(asm, fctx, labels, ty, p));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), fctx.layout[&uid]));
        }
    }
}

fn compile_terminator<'ll>(fctx: &FunctionContext<'ll>, labels: &mut StrInterner<Label>, mut asm: CodeBlock, term: ll::Terminator<'ll>) -> CodeBlock {
    match term {
        ll::Terminator::Ret(_ty, var) => {
            if let Some(var) = var {
                asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rax), var));
            }
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rbp), Op::Reg(Reg::Rsp)));
            asm.insns.push(Insn::Pop(Op::Reg(Reg::Rbp)));
            asm.insns.push(Insn::Ret);
        }
        ll::Terminator::Br(lbl) => {
            asm.insns.push(Insn::Jmp(Op::Imm(Imm::Lbl(make_local_label(labels, fctx, lbl)))));
        }
        ll::Terminator::Cbr(op, true_lbl, false_lbl) => {
            asm.insns.push(compile_operand(fctx, labels, Op::Reg(Reg::Rax), op));
            asm.insns.push(Insn::Cmp(Op::Imm(Imm::Word(0)), Op::Reg(Reg::Rax)));
            asm.insns.push(Insn::J(Cond::Eq, Op::Imm(Imm::Lbl(make_local_label(labels, fctx, false_lbl)))));
            asm.insns.push(Insn::Jmp(Op::Imm(Imm::Lbl(make_local_label(labels, fctx, true_lbl)))));
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

fn compile_operand<'ll>(fctx: &FunctionContext<'ll>, labels: &mut StrInterner<Label>, dst: Op, src: ll::Operand<'ll>) -> Insn {
    match src {
        ll::Operand::Gid(_) => Insn::Lea(translate_op(fctx, labels, src), dst),
        _ => Insn::Mov(translate_op(fctx, labels, src), dst),
    }
}

fn translate_op<'ll>(fctx: &FunctionContext<'ll>, labels: &mut StrInterner<Label>, op: ll::Operand<'ll>) -> Op {
    match op {
        ll::Operand::Null => Op::Imm(Imm::Word(0)),
        ll::Operand::Const(c) => Op::Imm(Imm::Word(c)),
        ll::Operand::Gid(gid) => Op::Ind3(Imm::Lbl(make_global_label(labels, &gid)), Reg::Rip),
        ll::Operand::Id(uid) => fctx.layout[&uid],
    }
}
