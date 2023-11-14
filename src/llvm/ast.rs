use core::fmt;
use std::collections::HashMap;

pub type Uid = String;

pub type Gid = String;

pub type Tid = String;

pub type Lbl = String;

#[derive(Clone, Debug, PartialEq)]
pub enum Ty {
    Void,
    I1,
    I8,
    I64,
    Ptr(Box<Ty>),
    Struct(Vec<Ty>),
    Array(i64, Box<Ty>),
    // strange redundancy with `FunTy` to avoid extra boxing
    Fun(Vec<Ty>, Box<Ty>),
    Named(Tid),
}

#[derive(Debug)]
pub struct FunTy {
    pub params: Vec<Ty>,
    pub ret: Ty,
}

#[derive(Debug)]
pub enum Operand {
    Null,
    Const(i64),
    Gid(Gid),
    Id(Uid),
}

#[derive(Clone, Copy, Debug)]
pub enum Bop {
    Add,
    Sub,
    Mul,
    Shl,
    Lshr,
    Ashr,
    And,
    Or,
    Xor,
}

#[derive(Clone, Copy, Debug)]
pub enum Cnd {
    Eq,
    Ne,
    Slt,
    Sle,
    Sgt,
    Sge,
}

#[derive(Debug)]
pub enum Insn {
    Binop(Bop, Ty, Operand, Operand),
    Alloca(Ty),
    Load(Ty, Operand),
    Store(Ty, Operand, Operand),
    Icmp(Cnd, Ty, Operand, Operand),
    Call(Ty, Operand, Vec<(Ty, Operand)>),
    Bitcast(Ty, Operand, Ty),
    Gep(Ty, Operand, Vec<Operand>),
}

#[derive(Debug)]
pub enum Terminator {
    Ret(Ty, Option<Operand>),
    Br(Lbl),
    Cbr(Operand, Lbl, Lbl),
}

#[derive(Debug)]
pub struct Block {
    pub insns: Vec<(Uid, Insn)>,
    pub term: (Uid, Terminator),
}

#[derive(Debug)]
pub struct Cfg {
    pub entry: Block, 
    pub blocks: Vec<(Lbl, Block)>,
}

#[derive(Debug)]
pub struct Fdecl {
    pub ty: FunTy,
    pub params: Vec<Uid>,
    pub cfg: Cfg,
}

#[derive(Clone, Debug)]
pub enum Ginit {
    Null,
    Gid(Gid),
    Int(i64),
    String(String),
    Array(Vec<(Ty, Ginit)>),
    Struct(Vec<(Ty, Ginit)>),
    Bitcast(Ty, Box<Ginit>, Ty),
}

pub type Gdecl = (Ty, Ginit);

#[derive(Debug)]
pub struct Prog {
    pub tdecls: HashMap<Tid, Ty>,
    pub gdecls: Vec<(Gid, Gdecl)>,
    pub fdecls: Vec<(Gid, Fdecl)>,
    pub edecls: Vec<(Gid, Ty)>,
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Void => write!(f, "void"),
            Ty::I1 => write!(f, "i1"),
            Ty::I8 => write!(f, "i8"),
            Ty::I64 => write!(f, "i64"),
            Ty::Ptr(t) => write!(f, "{t}*"),
            Ty::Struct(ts) => { 
                write!(f, "{{ ")?;
                super::write_separated(f, ", ", ts)?;
                write!(f, " }}")
            }
            Ty::Array(n, t) => write!(f, "[{n} x {t}]"),
            Ty::Fun(ts, t) => {
                write!(f, "{t} (")?;
                super::write_separated(f, ", ", ts)?;
                write!(f, ")")
            }
            Ty::Named(name) => write!(f, "%{name}"),
        }
    }
}
