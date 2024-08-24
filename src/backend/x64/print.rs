use std::io;
use std::fmt;

use super::ast::*;

pub fn write<W: io::Write>(mut w: W, prog: &Prog) -> io::Result<()> {
    if !prog.data.is_empty() {
        writeln!(w, "\t.data")?;
    }
    for datum in &prog.data {
        write_data_block(&mut w, &prog.labels, datum)?;
    }

    if !prog.code.is_empty() {
        writeln!(w, "\t.text")?;
    }
    for code in &prog.code {
        write_code_block(&mut w, &prog.labels, code)?;
    }

    Ok(())
}

fn write_data_block<W: io::Write>(w: &mut W, labels: &[Box<str>], db: &DataBlock) -> io::Result<()> {
    if db.global {
        writeln!(w, "\t.globl {}", labels[db.label])?;
    }
    writeln!(w, "{}:", labels[db.label])?;
    for datum in &db.data {
        match datum {
            Data::Quad(imm) => {
                write!(w, "\t.quad\t")?;
                write_imm(w, labels, *imm)?;
                writeln!(w)?;
            }
            // todo: escape?
            Data::String(s) => if s.ends_with('\0') {
                let s = &s[..s.len() - 1];
                writeln!(w, "\t.asciz\t\"{s}\"")?
            } else {
                writeln!(w, "\t.ascii\t\"{s}\"")?
            }
        }
    }

    Ok(())
}

fn write_code_block<W: io::Write>(w: &mut W, labels: &[Box<str>], cb: &CodeBlock) -> io::Result<()> {
    if cb.global {
        writeln!(w, "\t.globl {}", labels[cb.label])?;
    }
    writeln!(w, "{}:", labels[cb.label])?;
    for insn in &cb.insns {
        write!(w, "\t")?;
        write_insn(w, labels, insn)?;
        writeln!(w)?;
    }
    Ok(())
}

fn write_insn<W: io::Write>(w: &mut W, labels: &[Box<str>], insn: &Insn) -> io::Result<()> {
    match insn {
        Insn::Neg(o) => write_unary_insn(w, labels, "negq\t", *o),
        Insn::Add(o1, o2) => write_binary_insn(w, labels, "addq\t", *o1, *o2),
        Insn::Sub(o1, o2) => write_binary_insn(w, labels, "subq\t", *o1, *o2),
        Insn::Imul(o1, reg) => write_binary_insn(w, labels, "imulq\t", *o1, Op::Reg(*reg)),
        Insn::Inc(o) => write_unary_insn(w, labels, "incq\t", *o),
        Insn::Dec(o) => write_unary_insn(w, labels, "decq\t", *o),
        Insn::Not(o) => write_unary_insn(w, labels, "notq\t", *o),
        Insn::And(o1, o2) => write_binary_insn(w, labels, "andq\t", *o1, *o2),
        Insn::Or(o1, o2) => write_binary_insn(w, labels, "orq\t", *o1, *o2),
        Insn::Xor(o1, o2) => write_binary_insn(w, labels, "xorq\t", *o1, *o2),
        Insn::Lea(o1, o2) => write_binary_insn(w, labels, "leaq\t", *o1, *o2),
        Insn::Mov(o1, o2) => write_binary_insn(w, labels, "movq\t", *o1, *o2),
        Insn::Push(o) => write_unary_insn(w, labels, "pushq\t", *o),
        Insn::Pop(o) => write_unary_insn(w, labels, "popq\t", *o),
        Insn::Cmp(o1, o2) => write_binary_insn(w, labels, "cmpq\t", *o1, *o2),
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

            match *op {
                Op::Imm(imm) => write_imm(w, labels, imm),
                Op::Reg(reg) => write!(w, "*{reg}"),
                Op::Ind1(imm) => {
                    write!(w, "*")?;
                    write_imm(w, labels, imm)
                }
                Op::Ind2(reg) => write!(w, "*({reg})"),
                Op::Ind3(imm, reg) => {
                    write!(w, "*")?;
                    write_imm(w, labels, imm)?;
                    write!(w, "({reg})")
                }
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
            match *o1 {
                Op::Imm(_) => {
                    write!(w, "{opcode}\t")?;
                    write_op(w, labels, *o1)?;
                    write!(w, ", ")?;
                    write_op(w, labels, *o2)
                }
                Op::Reg(Reg::Rcx) => {
                    write!(w, "{opcode}\t%cl, ")?;
                    write_op(w, labels, *o2)
                }
                _ => unreachable!("shift operation with invalid operands"),
            }
        }
        // special handling for byte registers
        Insn::Set(cnd, op) => {
            write!(w, "set{cnd}\t")?;
            match *op {
                Op::Reg(r) => write!(w, "{}", byte_reg(r)),
                op => write_op(w, labels, op),
            }
        }
    }
}

fn write_unary_insn<W: io::Write>(w: &mut W, labels: &[Box<str>], s: &str, op: Op) -> io::Result<()> {
    write!(w, "{s}")?;
    write_op(w, labels, op)
}

fn write_binary_insn<W: io::Write>(w: &mut W, labels: &[Box<str>], s: &str, o1: Op, o2: Op) -> io::Result<()> {
    write!(w, "{s}")?;
    write_op(w, labels, o1)?;
    write!(w, ", ")?;
    write_op(w, labels, o2)
}

fn write_op<W: io::Write>(w: &mut W, labels: &[Box<str>], op: Op) -> io::Result<()> {
    match op {
        Op::Imm(imm) => {
            write!(w, "$")?;
            write_imm(w, labels, imm)
        }
        Op::Reg(reg) => write!(w, "{reg}"),
        Op::Ind1(imm) => write_imm(w, labels, imm),
        Op::Ind2(reg) => write!(w, "({reg})"),
        Op::Ind3(imm, reg) => {
            write_imm(w, labels, imm)?;
            write!(w, "({reg})")
        }
    }
}

fn write_imm<W: io::Write>(w: &mut W, labels: &[Box<str>], imm: Imm) -> io::Result<()> {
    match imm {
        Imm::Word(x) => write!(w, "{x}"),
        Imm::Lbl(ix) => write!(w, "{}", labels[ix]),
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
