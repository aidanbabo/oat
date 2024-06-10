use internment::Arena;
use std::collections::HashMap;

use crate::llvm::ast as ll;
use super::ast::*;

type Layout<'ll> = HashMap<ll::Uid<'ll>, Op<'static>>;

struct FunctionContext<'ll, 'asm> {
    arena: &'asm Arena<str>,
    layout: Layout<'ll>,
    name: ll::Lbl<'ll>,
}

pub fn x64_from_llvm<'asm>(ll: ll::Prog, arena: &'asm Arena<str>) -> Prog<'asm> {
    let mut p = Prog {
        code: Vec::new(),
        data: Vec::new(),
    };

    assert!(ll.tdecls.is_empty(), "no support for tdecls");
    assert!(ll.gdecls.is_empty(), "no support for gdecls");
    // assert!(ll.edecls.is_empty(), "no support for edecls");

    for (name, fdecl) in ll.fdecls {
        let (arg_layout, stack_layout) = layout(&fdecl);

        let fctx = FunctionContext {
            arena,
            layout: stack_layout,
            name,
        };

        let code_blocks = compile_function(fctx, arg_layout, name, fdecl);
        p.code.extend(code_blocks);
    }
    p
}

fn compile_function<'ll, 'asm>(fctx: FunctionContext<'ll, 'asm>, arg_layout: Layout<'ll>, name: ll::Gid<'ll>, fdecl: ll::Fdecl<'ll>) -> Vec<CodeBlock<'asm>> {
    let stack_size = fctx.layout.len();

    let mut b1 = CodeBlock {
        global: true,
        label: fctx.arena.intern(&name),
        insns: vec![
            Insn::Push(Op::Reg(Reg::Rbp)),
            Insn::Mov(Op::Reg(Reg::Rsp), Op::Reg(Reg::Rbp)),
            Insn::Sub(Op::Imm(Imm::Word(8 * stack_size as i64)), Op::Reg(Reg::Rsp)),
        ],
    };

    // move register args to their stack slots so they don't get clobbered
    // hashmaps have no order so this is kind of silly looking sometimes
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
        let compiled_block = compile_labelled_block(&fctx, lbl, b);
        blocks.push(compiled_block);
    }
    blocks
}

fn layout<'ll>(fdecl: &ll::Fdecl<'ll>) -> (Layout<'ll>, Layout<'ll>) {
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
        ll::Insn::Binop(_, _, _, _) => todo!(),
        ll::Insn::Alloca(_) => {
            asm.insns.push(Insn::Sub(Op::Imm(Imm::Word(8)), Op::Reg(Reg::Rsp)));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rsp), fctx.layout[&uid]));
        }
        ll::Insn::Load(_, _) => todo!(),
        ll::Insn::Store(_, src, dst) => {
            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rax), src));
            asm.insns.push(compile_operand(fctx, Op::Reg(Reg::Rcx), dst));
            asm.insns.push(Insn::Mov(Op::Reg(Reg::Rax), Op::Ind2(Reg::Rcx)));
        }
        ll::Insn::Icmp(_, _, _, _) => todo!(),
        ll::Insn::Call(_, _, _) => todo!(),
        ll::Insn::Bitcast(_, _, _) => todo!(),
        ll::Insn::Gep(_, _, _) => todo!(),
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
        ll::Terminator::Cbr(_, _, _) => todo!(),
    }

    asm
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
        ll::Operand::Gid(gid) => Op::Ind3(Imm::Lbl(fctx.arena.intern(&gid)), Reg::Rip),
        ll::Operand::Id(uid) => fctx.layout[&uid],
    }
}
