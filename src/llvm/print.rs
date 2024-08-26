use super::ast::*;
use std::fmt;
use std::io;

pub fn write<W: io::Write>(mut w: W, prog: &Prog) -> io::Result<()> {
    write_prog(&mut w, &prog.tables, prog)
}

pub(crate) fn write_separated<T, W, I, F>(w: &mut W, tables: &LookupTables, sep: &str, ts: I, mut printer: F) -> io::Result<()> 
    where W: io::Write,
          I: IntoIterator<Item = T>,
          F: FnMut(&mut W, &LookupTables, T) -> io::Result<()>,
{
    let mut first = true;
    for t in ts {
        if first {
            printer(w, tables, t)?;
        } else {
            write!(w, "{sep}")?;
            printer(w, tables, t)?;
        }
        first = false;
    }
    Ok(())
}

fn write_ty<W: io::Write>(w: &mut W, tables: &LookupTables, ty: &Ty) -> io::Result<()> {
    match ty {
        Ty::Void => write!(w, "void"),
        Ty::I1 => write!(w, "i1"),
        Ty::I8 => write!(w, "i8"),
        Ty::I64 => write!(w, "i64"),
        Ty::Ptr(t) => {
            write_ty(w, tables, t)?;
            write!(w, "*")
        }
        Ty::Struct(ts) => { 
            write!(w, "{{ ")?;
            write_separated(w, tables, ", ", ts, write_ty)?;
            write!(w, " }}")
        }
        Ty::Array(n, t) => {
            write!(w, "[{n} x ")?;
            write_ty(w, tables, t)?;
            write!(w, "]")
        }
        Ty::Fun(ts, t) => {
            write_ty(w, tables, t)?;
            write!(w, " (")?;
            write_separated(w, tables, ", ", ts, write_ty)?;
            write!(w, ")")
        }
        Ty::Named(id) => write!(w, "%{}", tables.types[id.ix()]),
    }
}

fn write_op<W: io::Write>(w: &mut W, tables: &LookupTables, op: &Operand<'_>) -> io::Result<()> {
    match *op {
        Operand::Null => write!(w, "null"),
        Operand::Const(x) => write!(w, "{x}"),
        Operand::Gid(g) => write!(w, "@{}", tables.globals[g.ix()]),
        Operand::Id(u) => write!(w, "%{u}"),
    }
}

impl fmt::Display for Bop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Bop::Add => write!(f, "add"),
            Bop::Sub => write!(f, "sub"),
            Bop::Mul => write!(f, "mul"),
            Bop::Shl => write!(f, "shl"),
            Bop::Lshr => write!(f, "lshr"),
            Bop::Ashr => write!(f, "ashr"),
            Bop::And => write!(f, "and"),
            Bop::Or => write!(f, "or"),
            Bop::Xor => write!(f, "xor"),
        }
    }
}

impl fmt::Display for Cnd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Cnd::Eq => write!(f, "eq"),
            Cnd::Ne => write!(f, "ne"),
            Cnd::Slt => write!(f, "slt"),
            Cnd::Sle => write!(f, "sle"),
            Cnd::Sgt => write!(f, "sgt"),
            Cnd::Sge => write!(f, "sge"),
        }
    }
}


fn write_insn<W: io::Write>(w: &mut W, tables: &LookupTables, insn: &Insn<'_>) -> io::Result<()> {
    match insn {
        Insn::Binop(b, t, o1, o2) => {
            write!(w, "{b} ")?;
            write_ty(w, tables, t)?;
            write!(w, " ")?;
            write_op(w, tables, o1)?;
            write!(w, ", ")?;
            write_op(w, tables, o2)
        }
        Insn::Alloca(t) => {
            write!(w, "alloca ")?;
            write_ty(w, tables, t)
        }
        Insn::Load(t, o) => {
            write!(w, "load ")?;
            write_ty(w, tables, t)?;
            write!(w, ", ")?;
            write_ty(w, tables, t)?;
            // added ptr
            write!(w, "* ")?;
            write_op(w, tables, o)
        }
        Insn::Store(t, os, od) => {
            write!(w, "store ")?;
            write_ty(w, tables, t)?;
            write!(w, " ")?;
            write_op(w, tables, os)?;
            write!(w, ", ")?;
            write_ty(w, tables, t)?;
            // added ptr
            write!(w, "* ")?;
            write_op(w, tables, od)
        }
        Insn::Icmp(c, t, o1, o2) => {
            write!(w, "icmp {c} ")?;
            write_ty(w, tables, t)?;
            write!(w, " ")?;
            write_op(w, tables, o1)?;
            write!(w, ", ")?;
            write_op(w, tables, o2)
        }
        Insn::Call(t, o, oa) => {
            write!(w, "call ")?;
            write_ty(w, tables, t)?;
            write!(w, " ")?;
            write_op(w, tables, o)?;
            write!(w, "(")?;
            write_separated(w, tables, ", ", oa, |w, tables, (t, o)| {
                write_ty(w, tables, t)?;
                write!(w, " ")?;
                write_op(w, tables, o)
            })?;
            write!(w, ")")
        }
        Insn::Bitcast(t1, o, t2) => {
            write!(w, "bitcast ")?;
            write_ty(w, tables, t1)?;
            write!(w, " ")?;
            write_op(w, tables, o)?;
            write!(w, " to ")?;
            write_ty(w, tables, t2)
        }
        Insn::Gep(t, o, oi) => {
            write!(w, "getelementptr ")?;
            write_ty(w, tables, t)?;
            write!(w, ", ")?;
            write_ty(w, tables, t)?;
            // added ptr
            write!(w, "* ")?;
            write_op(w, tables, o)?;
            for o in oi {
                match o {
                    Operand::Const(i) => write!(w, ", i32 {i}")?,
                    o => {
                        write!(w, ", i64 ")?;
                        write_op(w, tables, o)?;
                    }
                }
            }
            Ok(())
        }
    }
}

fn write_label<W: io::Write>(w: &mut W, tables: &LookupTables, lid: Lbl) -> io::Result<()> {
    write!(w, "{}", tables.labels[lid.ix()])
}

fn write_term<W: io::Write>(w: &mut W, tables: &LookupTables, term: &Terminator<'_>) -> io::Result<()> {
    match term {
        Terminator::Ret(_, None) => write!(w, "ret void"),
        Terminator::Ret(t, Some(o)) => {
            write!(w, "ret ")?;
            write_ty(w, tables, t)?;
            write!(w, " ")?;
            write_op(w, tables, o)
        }
        Terminator::Br(l) => {
            write!(w, "br label %")?;
            write_label(w, tables, *l)
        }
        Terminator::Cbr(o, l, m) => {
            write!(w, "br i1 ")?;
            write_op(w, tables, o)?;
            write!(w, ", label %")?;
            write_label(w, tables, *l)?;
            write!(w, ", label %")?;
            write_label(w, tables, *m)
        }
    }
}

fn write_block<W: io::Write>(w: &mut W, tables: &LookupTables, block: &Block<'_>) -> io::Result<()> {
    for (u, i) in &block.insns {
        match i {
            Insn::Store(_, _, _) | Insn::Call(Ty::Void, _, _) => write!(w, "\t")?,
            _ => write!(w, "\t%{u} = ")?,
        }
        write_insn(w, tables, i)?;
        writeln!(w)?;
    }
    write!(w, "\t")?;
    write_term(w, tables, &block.term.1)?;
    writeln!(w)
}

fn write_cfg<W: io::Write>(w: &mut W, tables: &LookupTables, cfg: &Cfg<'_>) -> io::Result<()> {
    write_block(w, tables, &cfg.entry)?;
    for (label, b) in &cfg.blocks {
        write_label(w, tables, *label)?;
        writeln!(w, ":")?;
        write_block(w, tables, b)?;
    }
    Ok(())
}

fn write_ginit<W: io::Write>(w: &mut W, tables: &LookupTables, ginit: &Ginit) -> io::Result<()> {
    match ginit {
        Ginit::Null => write!(w, "null"),
        Ginit::Gid(g) => write!(w, "@{}", tables.globals[g.ix()]),
        Ginit::Int(i) => write!(w, "{i}"),
        Ginit::String(s) => {
            if s.ends_with('\0') {
                write!(w, "c\"{s}\"")
            } else {
                write!(w, "c\"{s}\\00\"")
            }
        },
        Ginit::Array(gis) => {
            write!(w, "[")?;
            write_separated(w, tables, ", ", gis, |w, tables, (t, init)| {
                write_ty(w, tables, t)?;
                write!(w, " ")?;
                write_ginit(w, tables, init)
            })?;
            write!(w, "]")
        }
        Ginit::Struct(gis) => {
            write!(w, "{{")?;
            write_separated(w, tables, ", ", gis, |w, tables, (t, init)| {
                write_ty(w, tables, t)?;
                write!(w, " ")?;
                write_ginit(w, tables, init)
            })?;
            write!(w, "}}")
        }
        Ginit::Bitcast(t1, g, t2) => {
            write!(w, "bitcast (")?;
            write_ty(w, tables, t1)?;
            write!(w, " ")?;
            write_ginit(w, tables, g)?;
            write!(w, " to ")?;
            write_ty(w, tables, t2)?;
            write!(w, ")")
        }
    }
}

fn write_prog<W: io::Write>(w: &mut W, tables: &LookupTables, prog: &Prog<'_>) -> io::Result<()> {
    // bug: todo: order these so there are no forward declarations to non-struct types
    for (tid, t) in &prog.tdecls {
        write!(w, "%{} = type ", tables.types[tid.ix()])?;
        write_ty(w, tables,t)?;
        writeln!(w)?;
    }
    if !prog.tdecls.is_empty() {
        writeln!(w)?;
    }

    for (gid, (ty, init)) in &prog.gdecls {
        write!(w, "@{} = global ", tables.globals[gid.ix()])?;
        write_ty(w, tables, ty)?;
        write!(w, " ")?;
        write_ginit(w, tables, init)?;
        writeln!(w)?;
    }
    if !prog.gdecls.is_empty() {
        writeln!(w)?;
    }

    for (gid, fd) in &prog.fdecls {
        write!(w, "define ")?;
        write_ty(w, tables, &fd.ty.ret)?;
        write!(w, " @{}(", tables.globals[gid.ix()])?;
        write_separated(w, tables, ", ", fd.ty.params.iter().zip(fd.params.iter()), |w, tables, (t, o)| {
            write_ty(w, tables, t)?;
            write!(w, " %{o}")
        })?;
        writeln!(w, ") {{")?;
        write_cfg(w, tables, &fd.cfg)?;
        writeln!(w, "}}")?;
    }
    if !prog.fdecls.is_empty() {
        writeln!(w)?;
    }

    for (g, t) in &prog.edecls {
        match t {
            Ty::Fun(ts, rt) => {
                write!(w, "declare ")?;
                write_ty(w, tables, rt)?;
                write!(w, " @{}(", tables.globals[g.ix()])?;
                write_separated(w, tables, ", ", ts, write_ty)?;
                writeln!(w, ")")?;
            }
            _ => {
                write!(w, "@{} = external global ", tables.globals[g.ix()])?;
                write_ty(w, tables, t)?;
                writeln!(w)?;
            }
        }
    }

    Ok(())
}
