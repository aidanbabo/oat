use std::io;
use std::fmt;

use super::ast::*;

pub fn write<W: io::Write>(mut w: W, prog: &Prog) -> io::Result<()> {
    if !prog.data.is_empty() {
        writeln!(w, "\t.data")?;
    }
    for datum in &prog.data {
        write_data_block(&mut w, datum)?;
    }

    if !prog.code.is_empty() {
        writeln!(w, "\t.text")?;
    }
    for code in &prog.code {
        write_code_block(&mut w, code)?;
    }

    Ok(())
}

fn write_data_block<W: io::Write>(w: &mut W, db: &DataBlock) -> io::Result<()> {
    if db.global {
        writeln!(w, "\t.globl {}", db.label)?;
    }
    writeln!(w, "{}:", db.label)?;
    for datum in &db.data {
        match datum {
            Data::Quad(imm) => writeln!(w, "\t.quad\t{imm}")?,
            // todo: escape?
            Data::String(s) => writeln!(w, "\t.asciz\t\"{s}\"")?,
        }
    }

    Ok(())
}

fn write_code_block<W: io::Write>(w: &mut W, cb: &CodeBlock) -> io::Result<()> {
    if cb.global {
        writeln!(w, "\t.globl {}", cb.label)?;
    }
    writeln!(w, "{}:", cb.label)?;
    for insn in &cb.insns {
        write!(w, "\t")?;
        write_insn(w, insn)?;
        writeln!(w)?;
    }
    Ok(())
}

fn write_insn<W: io::Write>(w: &mut W, insn: &Insn) -> io::Result<()> {
    match insn {
        Insn::Neg(op) => write!(w, "negq\t{op}"),
        Insn::Add(o1, o2) => write!(w, "addq\t{o1}, {o2}"),
        Insn::Sub(o1, o2) => write!(w, "subq\t{o1}, {o2}"),
        Insn::Imul(o1, o2) => write!(w, "imulq\t{o1}, {o2}"),
        Insn::Inc(o) => write!(w, "incq\t{o}"),
        Insn::Dec(o) => write!(w, "decq\t{o}"),
        Insn::Not(o) => write!(w, "notq\t{o}"),
        Insn::And(o1, o2) => write!(w, "andq\t{o1}, {o2}"),
        Insn::Or(o1, o2) => write!(w, "orq\t{o1}, {o2}"),
        Insn::Xor(o1, o2) => write!(w, "xorq\t{o1}, {o2}"),
        Insn::Lea(o1, o2) => write!(w, "leaq\t{o1}, {o2}"),
        Insn::Mov(o1, o2) => write!(w, "movq\t{o1}, {o2}"),
        Insn::Push(o) => write!(w, "pushq\t{o}"),
        Insn::Pop(o) => write!(w, "popq\t{o}"),
        Insn::Cmp(o1, o2) => write!(w, "cmpq\t{o1}, {o2}"),
        Insn::Ret => write!(w, "retq"),
        // special handling for jumps
        Insn::Jmp(..) | Insn::J(..) | Insn::Call(..) => {
            let op = match insn {
                Insn::Jmp(op) => {
                    write!(w, "jmp\t")?;
                    op
                }
                Insn::J(cnd, op) => {
                    write!(w, "j{cnd}\t")?;
                    op
                },
                Insn::Call(op) => {
                    write!(w, "callq\t")?;
                    op
                }
                _ => unreachable!(),
            };

            match op {
                Op::Imm(imm) => write!(w, "{imm}"),
                Op::Reg(reg) => write!(w, "*{reg}"),
                Op::Ind1(imm) => write!(w, "*{imm}"),
                Op::Ind2(reg) => write!(w, "*({reg})"),
                Op::Ind3(imm, reg) => write!(w, "*{imm}({reg})"),
            }
        }
        // special handling for shifts
        Insn::Sar(o1, o2) | Insn::Shl(o1, o2) | Insn::Shr(o1, o2) => {
            let opcode = match insn {
                Insn::Sar(..) => "sarq",
                Insn::Shl(..) => "shlq",
                Insn::Shr(..) => "shrq",
                _ => unreachable!(),
            };
            match o1 {
                Op::Imm(_) => write!(w, "{opcode}\t{o1}, {o2}"),
                Op::Reg(Reg::Rcx) => write!(w, "{opcode}\t%cl, {o2}"),
                _ => unreachable!("shift operation with invalid operands"),
            }
        }
        // special handling for byte registers
        Insn::Set(cnd, op) => {
            write!(w, "set{cnd}\t")?;
            match op {
                Op::Reg(r) => write!(w, "{}", byte_reg(*r)),
                _ => write!(w, "{op}"),
            }
        }
    }
}

impl fmt::Display for Op<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op::Imm(imm) => write!(f, "${imm}"),
            Op::Reg(reg) => write!(f, "{reg}"),
            Op::Ind1(imm) => write!(f, "{imm}"),
            Op::Ind2(reg) => write!(f, "({reg})"),
            Op::Ind3(imm, reg) => write!(f, "{imm}({reg})"),
        }
    }
}

impl fmt::Display for Imm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Imm::Word(w) => write!(f, "{w}"),
            Imm::Lbl(l) => write!(f, "{l}"),
        }
    }
}

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Reg::Rax => write!(f, "%rax"),
            Reg::Rbx => write!(f, "%rbx"),
            Reg::Rcx => write!(f, "%rcx"),
            Reg::Rdx => write!(f, "%rdx"),
            Reg::Rsi => write!(f, "%rsi"),
            Reg::Rdi => write!(f, "%rdi"),
            Reg::Rbp => write!(f, "%rbp"),
            Reg::Rsp => write!(f, "%rsp"),
            Reg::R8 => write!(f, "%r8"),
            Reg::R9 => write!(f, "%r9"),
            Reg::R10 => write!(f, "%r10"),
            Reg::R11 => write!(f, "%r11"),
            Reg::R12 => write!(f, "%r12"),
            Reg::R13 => write!(f, "%r13"),
            Reg::R14 => write!(f, "%r14"),
            Reg::R15 => write!(f, "%r15"),
            Reg::Rip => write!(f, "%rip"),
        }
    }
}

fn byte_reg(r: Reg) -> &'static str {
    match r {
        Reg::Rax => "%al",
        Reg::Rbx => "%bl",
        Reg::Rcx => "%cl",
        Reg::Rdx => "%dl",
        Reg::Rsi => "%sil",
        Reg::Rdi => "%dil",
        Reg::Rbp => "%bpl",
        Reg::Rsp => "%spl",
        Reg::R8 => "%r8b",
        Reg::R9 => "%r9b",
        Reg::R10 => "%r10b",
        Reg::R11 => "%r11b",
        Reg::R12 => "%r12b",
        Reg::R13 => "%r13b",
        Reg::R14 => "%r14b",
        Reg::R15 => "%r15b",
        Reg::Rip => "%rip",
    }
}

impl fmt::Display for Cond {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Cond::Eq => write!(f, "e"),
            Cond::Neq => write!(f, "ne"),
            Cond::Lt => write!(f, "l"),
            Cond::Le => write!(f, "le"),
            Cond::Gt => write!(f, "g"),
            Cond::Ge => write!(f, "ge"),
        }
    }
}
