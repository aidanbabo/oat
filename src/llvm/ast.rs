use internment::ArenaIntern;

use std::collections::HashMap;
use std::convert::From;

// todo: change uid to an integer
// this will involve using lookup tables to match to the string name
// this will also mean that analysis will probably have to change to not having
// a removal step and we'd need an "empty" instruction to allow analysis to go on without having to
// reshuffle everything
pub type Uid<'arena> = ArenaIntern<'arena, str>;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[repr(transparent)]
pub struct Gid(u32);

impl Gid {
    pub fn ix(self) -> usize {
        self.0 as usize
    }
}

impl From<u32> for Gid {
    fn from(value: u32) -> Self {
        Gid(value)
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[repr(transparent)]
pub struct Tid(u32);

impl Tid {
    pub fn ix(self) -> usize {
        self.0 as usize
    }
}

impl From<u32> for Tid {
    fn from(value: u32) -> Self {
        Tid(value)
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[repr(transparent)]
pub struct Lbl(u32);

impl Lbl {
    pub fn ix(self) -> usize {
        self.0 as usize
    }
}

impl From<u32> for Lbl {
    fn from(value: u32) -> Self {
        Lbl(value)
    }
}

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

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Operand<'arena> {
    Null,
    Const(i64),
    Gid(Gid),
    Id(Uid<'arena>),
}

#[derive(Clone, Copy, Debug, PartialEq)]
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

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Cnd {
    Eq,
    Ne,
    Slt,
    Sle,
    Sgt,
    Sge,
}

#[derive(Debug, PartialEq)]
pub enum Insn<'a> {
    Binop(Bop, Ty, Operand<'a>, Operand<'a>),
    Alloca(Ty),
    /// the type of the loaded value and then the operand to load from
    Load(Ty, Operand<'a>),
    /// the type of the stored value, the value operand to store, and the location to store to
    Store(Ty, Operand<'a>, Operand<'a>),
    Icmp(Cnd, Ty, Operand<'a>, Operand<'a>),
    Call(Ty, Operand<'a>, Vec<(Ty, Operand<'a>)>),
    Bitcast(Ty, Operand<'a>, Ty),
    /// the type pointed to, the value to index from, and the index values
    Gep(Ty, Operand<'a>, Vec<Operand<'a>>),
}

#[derive(Debug, PartialEq)]
pub enum Terminator<'a> {
    /// return type and optional return value
    /// required if the return type is not void
    Ret(Ty, Option<Operand<'a>>),
    /// label to branch to
    Br(Lbl),
    /// the operand to branch on and then the true and false labels
    Cbr(Operand<'a>, Lbl, Lbl),
}

#[derive(Debug)]
pub struct Block<'a> {
    pub insns: Vec<(Uid<'a>, Insn<'a>)>,
    pub term: (Uid<'a>, Terminator<'a>),
}

#[derive(Debug)]
pub struct Cfg<'a> {
    pub entry: Block<'a>, 
    pub blocks: Vec<(Lbl, Block<'a>)>,
}

#[derive(Debug)]
pub struct Fdecl<'a> {
    pub ty: FunTy,
    pub params: Vec<Uid<'a>>,
    pub cfg: Cfg<'a>,
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

#[derive(Debug, Default)]
pub struct LookupTables {
    pub labels: Vec<Box<str>>,
    pub types: Vec<Box<str>>,
    pub globals: Vec<Box<str>>,
}

#[derive(Debug, Default)]
pub struct Prog<'a> {
    // todo: make tdecls a vec!
    pub tdecls: HashMap<Tid, Ty>,
    pub gdecls: Vec<(Gid, Gdecl)>,
    pub fdecls: Vec<(Gid, Fdecl<'a>)>,
    pub edecls: Vec<(Gid, Ty)>,
    pub tables: LookupTables,
}
