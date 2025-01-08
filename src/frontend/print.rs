// todo: parse separated, but better than the one for the llvm parser

use std::io;
use std::fmt;

use super::ast::*;
use super::Node;

const INDENT: &str = "    ";

fn do_indent<W: io::Write>(w: &mut W, indent: i32) -> io::Result<()> {
    for _ in 0..indent {
        write!(w, "{INDENT}")?;
    }
    Ok(())
}

pub fn write<W: io::Write>(mut w: W, prog: &Prog) -> io::Result<()> {
    for decl in prog {
        match decl {
            Decl::Var(v) => write_global(&mut w, v)?,
            Decl::Fun(f) => write_fun(&mut w, f)?,
            Decl::Type(t) => write_type(&mut w, t)?,
        }
    }
    Ok(())
}

fn write_global<W: io::Write>(w: &mut W, g: &Gdecl) -> io::Result<()> {
    writeln!(w, "global {} = {};", g.name, g.init.t)
}

fn write_fun<W: io::Write>(w: &mut W, f: &Fdecl) -> io::Result<()> {
    write!(w, "{} {}(", f.ret_ty, f.name)?;
    let mut first = true;
    for (t, n) in &f.args {
        if !first {
            write!(w, ", ")?;
        }
        write!(w, "{} {}", t, n)?;
        first = false;
    }
    write!(w, ") ")?;
    write_block(w, &f.body, 0)?;
    writeln!(w)
}

fn write_block<W: io::Write>(w: &mut W, body: &[Node<Stmt>], indent: i32) -> io::Result<()> {
    writeln!(w, "{{")?;
    for s in body {
        do_indent(w, indent + 1)?;
        write_stmt(w, s, indent + 1)?;
        writeln!(w)?;
    }
    do_indent(w, indent)?;
    write!(w, "}}")
}

fn write_stmt<W: io::Write>(w: &mut W, s: &Stmt, indent: i32) -> io::Result<()> {
    match s {
        Stmt::Assn(id, e) => write!(w, "{} = {};", **id, **e)?,
        Stmt::Decl(d) => write!(w, "{d};")?,
        Stmt::Ret(Some(v)) => write!(w, "return {};", **v)?,
        Stmt::Ret(None) => write!(w, "return;")?,
        Stmt::Call(fun, args) => {
            write!(w, "{}(", fun.t)?;
            let mut first = true;
            for a in args {
                if !first {
                    write!(w, ", ")?;
                }
                write!(w, "{}", a.t)?;
                first = false;
            }
            write!(w, ");")?
        }
        Stmt::If(..) | Stmt::IfNull(..) => write_if(w, s, indent)?,
        Stmt::For(vdecls, cnd, update, block) => {
            write!(w, "for (")?;
            let mut first = true;
            for vdecl in vdecls {
                if !first {
                    write!(w, ", ")?;
                }
                write!(w, "{}", vdecl)?;
                first = false;
            }
            write!(w, "; ")?;
            if let Some(cnd) = cnd {
                write!(w, "{}", cnd.t)?;
            }
            write!(w, "; ")?;
            if let Some(update) = update {
                write_stmt(w, update, indent)?;
            }
            write!(w, ") ")?;
            write_block(w, block, indent)?;
        }
        Stmt::While(cnd, block) => {
            write!(w, "while ({}) ", cnd.t)?;
            write_block(w, block, indent)?;
        }
    }
    Ok(())
}

fn write_if<W: io::Write>(w: &mut W, s: &Stmt, indent: i32) -> io::Result<()> {
    let else_blk = match s {
        Stmt::If(cnd, if_blk, else_blk) => {
            write!(w, "if ({}) ", cnd.t)?;
            write_block(w, if_blk, indent)?;
            else_blk
        }
        Stmt::IfNull(ty, id, exp, if_blk, else_blk) => {
            write!(w, "ifq ({} {} = {}) ", ty, id, exp.t)?;
            write_block(w, if_blk, indent)?;
            else_blk
        }
        _ => unreachable!(),
    };
    if !else_blk.is_empty() {
        write!(w, " else ")?;
        if let [Node { t: stmt@(Stmt::If(..) | Stmt::IfNull(..)), ..}] = &else_blk[..] {
            write_if(w, stmt, indent)?;
        } else {
            write_block(w, else_blk, indent)?;
        }
    }
    Ok(())
}

fn write_type<W: io::Write>(w: &mut W, t: &Tdecl) -> io::Result<()> {
    write!(w, "struct {} {{", t.name)?;
    if !t.fields.is_empty() {
        writeln!(w)?;
        for f in &t.fields {
            writeln!(w, "{INDENT}{} {};", f.ty, f.name)?;
        }
    }
    writeln!(w, "}}")
}

impl fmt::Display for Ty<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TyKind::Void => write!(f, "void")?,
            TyKind::Bool => write!(f, "bool")?,
            TyKind::Int => write!(f, "int")?,
            TyKind::String => write!(f, "string")?,
            TyKind::Struct(i) => write!(f, "{i}")?,
            TyKind::Array(t) => write!(f, "{t}[]")?,
            TyKind::Fun(args, ret) => {
                if self.nullable {
                    write!(f, "(")?;
                }
                write!(f, "(")?;
                let mut first = true;
                for arg in args {
                    if !first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                    first = false;
                }
                write!(f, ") -> {ret}")?;
                if self.nullable {
                    write!(f, ")")?;
                }
            }
        }
        if self.nullable {
            write!(f, "?")?;
        }
        Ok(())
    }
}

impl fmt::Display for Exp<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Exp::Null(t) => write!(f, "{t} null"),
            Exp::Bool(true) => write!(f, "true"),
            Exp::Bool(false) => write!(f, "false"),
            Exp::Int(n) => write!(f, "{n}"),
            Exp::Str(s) => write!(f, "\"{s}\""),
            Exp::Id(id) => write!(f, "{id}"),
            Exp::ArrElems(t, elems) => {
                write!(f, "new {t}[]{{")?;
                let mut first = true;
                for e in elems {
                    if !first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", e.t)?;
                    first = false;
                }
                write!(f, "}}")
            }
            Exp::ArrLen(t, len) => write!(f, "new {t}[{}]", len.t),
            Exp::ArrInit(t, len, id, exp) => write!(f, "new {t}[{}]{{{id} -> {}}}", len.t, exp.t),
            Exp::Index(a, i) => write!(f, "{}[{}]", a.t, i.t),
            Exp::Length(e) => write!(f, "length({})", e.t),
            Exp::Struct(n, fields) => {
                write!(f, "new {n}{{")?;
                let mut first = true;
                for (field, exp) in fields {
                    if !first {
                        write!(f, "; ")?;
                    }
                    write!(f, "{} = {}", field, exp.t)?;
                    first = false;
                }
                write!(f, "}}")
            }
            Exp::Proj(lhs, field) => write!(f, "{}.{}", lhs.t, field),
            Exp::Call(fun, args) => {
                write!(f, "{}(", fun.t)?;
                let mut first = true;
                for a in args {
                    if !first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", a.t)?;
                    first = false;
                }
                write!(f, ")")
            }
            Exp::Bop(b, lhs, rhs) => {
                if let Exp::Bop(..) = &lhs.t {
                    write!(f, "({})", lhs.t)?;
                } else {
                    write!(f, "{}", lhs.t)?;
                }
                write!(f, " {} ", b)?;
                if let Exp::Bop(..) = &rhs.t {
                    write!(f, "({})", rhs.t)?;
                } else {
                    write!(f, "{}", rhs.t)?;
                }
                Ok(())
            }
            Exp::Uop(u, e) => write!(f, "{}{}", u, e.t),
        }
    }
}

impl fmt::Display for Unop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Unop::Neg => "-",
            Unop::LogNot => "!",
            Unop::BitNot => "~",
        };
        write!(f, "{s}")
    }
}

impl fmt::Display for Binop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Binop::Add => "+",
            Binop::Sub => "-",
            Binop::Mul => "*",
            Binop::Eq => "==",
            Binop::Neq => "!=",
            Binop::Lt => "<",
            Binop::Lte => "<=",
            Binop::Gt => ">",
            Binop::Gte => ">=",
            Binop::And => "&",
            Binop::Or => "|",
            Binop::IAnd => "[&]",
            Binop::IOr => "[|]",
            Binop::Shl => "<<",
            Binop::Shr => ">>",
            Binop::Sar => ">>>",
        };
        write!(f, "{s}")
    }
}

impl fmt::Display for Vdecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "var {} = {}", self.name, *self.exp)
    }
}
