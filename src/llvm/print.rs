use super::ast::*;
use std::fmt;
use std::io;

pub fn write<W: io::Write>(mut w: W, prog: &Prog) -> io::Result<()> {
    write!(w, "{prog}")
}

pub struct Separated<'a, T, U>(pub &'static str, pub &'a (T, U));

impl<'a, T, U> fmt::Display for Separated<'a, T, U> 
where T: fmt::Display,
      U: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.1.0, self.0, self.1.1)
    }
}

pub(crate) fn write_separated<T, W>(f: &mut W, sep: &str, ts: impl IntoIterator<Item = T>) -> fmt::Result
    where T: fmt::Display,
          W: fmt::Write,
{
    let mut first = true;
    for t in ts {
        if first {
            write!(f, "{t}")?
        } else {
            write!(f, "{sep}{t}")?
        }
        first = false;
    }
    Ok(())
}

// This is to avoid allocating when printing pointers to types that we
// create. E.g. load stores the pointee not pointer and we must create it.
struct Ptr<T>(T);

impl<T: fmt::Display> fmt::Display for Ptr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}*", self.0)
    }
}

impl<'a> fmt::Display for Ty<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Void => write!(f, "void"),
            Ty::I1 => write!(f, "i1"),
            Ty::I8 => write!(f, "i8"),
            Ty::I64 => write!(f, "i64"),
            Ty::Ptr(t) => write!(f, "{}", Ptr(t)),
            Ty::Struct(ts) => { 
                write!(f, "{{ ")?;
                write_separated(f, ", ", ts)?;
                write!(f, " }}")
            }
            Ty::Array(n, t) => write!(f, "[{n} x {t}]"),
            Ty::Fun(ts, t) => {
                write!(f, "{t} (")?;
                write_separated(f, ", ", ts)?;
                write!(f, ")")
            }
            Ty::Named(name) => write!(f, "%{name}"),
        }
    }
}

impl<'a> fmt::Display for Operand<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Null => write!(f, "null"),
            Operand::Const(x) => write!(f, "{x}"),
            Operand::Gid(g) => write!(f, "@{g}"),
            Operand::Id(u) => write!(f, "%{u}"),
        }
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

impl<'a> fmt::Display for Insn<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Insn::Binop(b, t, o1, o2) => write!(f, "{b} {t} {o1}, {o2}"),
            Insn::Alloca(t) => write!(f, "alloca {t}"),
            Insn::Load(t, o) => write!(f, "load {t}, {} {o}", Ptr(t)),
            Insn::Store(t, os, od) => write!(f, "store {t} {os}, {} {od}", Ptr(t)),
            Insn::Icmp(c, t, o1, o2) => write!(f, "icmp {c} {t} {o1}, {o2}"),
            Insn::Call(t, o, oa) => {
                write!(f, "call {t} {o}(")?;
                let mut first = true;
                for (t, o) in oa {
                    if first {
                        write!(f, "{t} {o}")?
                    } else {
                        write!(f, ", {t} {o}")?
                    }
                    first = false;
                }
                write!(f, ")")
            }
            Insn::Bitcast(t1, o, t2) => write!(f, "bitcast {t1} {o} to {t2}"),
            Insn::Gep(t, o, oi) => {
                write!(f, "getelementptr {t}, {} {o}", Ptr(t))?;
                for o in oi {
                    match o {
                        Operand::Const(i) => write!(f, ", i32 {i}")?,
                        o => write!(f, ", i64 {o}")?,
                    }
                }
                Ok(())
            }
        }
    }
}

impl<'a> fmt::Display for Terminator<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Terminator::Ret(_, None) => write!(f, "ret void"),
            Terminator::Ret(t, Some(o)) => write!(f, "ret {t} {o}"),
            Terminator::Br(l) => write!(f, "br label %{l}"),
            Terminator::Cbr(o, l, m) => write!(f, "br i1 {o}, label %{l}, label %{m}"),
        }
    }
}

impl<'a> fmt::Display for Block<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (u, i) in &self.insns {
            match i {
                Insn::Store(_, _, _) | Insn::Call(Ty::Void, _, _) => write!(f, "\t")?,
                _ => write!(f, "\t%{u} = ")?,
            }
            writeln!(f, "{i}")?;
        }
        write!(f, "\t{}", self.term.1)
    }
}

impl<'a> fmt::Display for Cfg<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.entry)?;
        for (label, b) in &self.blocks {
            writeln!(f, "{label}:")?;
            writeln!(f, "{b}")?;
        }
        Ok(())
    }
}

impl<'a> fmt::Display for Ginit<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ginit::Null => write!(f, "null"),
            Ginit::Gid(g) => write!(f, "@{g}"),
            Ginit::Int(i) => write!(f, "{i}"),
            Ginit::String(s) => write!(f, "c\"{s}\\00\""),
            Ginit::Array(gis) => {
                write!(f, "[")?;
                write_separated(f, ", ", gis.iter().map(|t| Separated(" ", t)))?;
                write!(f, "]")
            }
            Ginit::Struct(gis) => {
                write!(f, "{{")?;
                write_separated(f, ", ", gis.iter().map(|t| Separated(" ", t)))?;
                write!(f, "}}")
            }
            Ginit::Bitcast(t1, g, t2) => write!(f, "bitcast ({t1} {g} to {t2})"),
        }
    }
}

impl<'a> fmt::Display for Prog<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (u, t) in &self.tdecls {
            writeln!(f, "%{u} = type {t}")?
        }
        if !self.tdecls.is_empty() {
            writeln!(f)?;
        }

        for (gid, (ty, init)) in &self.gdecls {
            writeln!(f, "@{gid} = global {ty} {init}")?;
        }
        if !self.gdecls.is_empty() {
            writeln!(f)?;
        }

        for (u, fd) in &self.fdecls {
            write!(f, "define {} @{}(", fd.ty.ret, u)?;
            let mut first = true;
            for (t, o) in fd.ty.params.iter().zip(fd.params.iter()) {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{t} %{o}")?;
                first = false;
            }
            write!(f, ") {{\n{}}}\n", fd.cfg)?;
        }
        if !self.fdecls.is_empty() {
            writeln!(f)?;
        }

        for (g, t) in &self.edecls {
            match t {
                Ty::Fun(ts, rt) => {
                    write!(f, "declare {rt} @{g}(")?;
                    write_separated(f, ", ", ts)?;
                    writeln!(f, ")")?;
                }
                _ => writeln!(f, "@{g} = external global {t}")?,
            }
        }

        Ok(())
    }
}
