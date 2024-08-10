use std::collections::HashMap;
use internment::ArenaIntern;

// todo: change uid to an integer
// this will involve using lookup tables to match to the string name
// this will also mean that analysis will probably have to change to not having
// a removal step and we'd need an "empty" instruction to allow analysis to go on without having to
// reshuffle everything
pub type Uid<'arena> = ArenaIntern<'arena, str>;
pub type Gid<'arena> = ArenaIntern<'arena, str>;
pub type Tid<'arena> = ArenaIntern<'arena, str>;
pub type Lbl<'arena> = ArenaIntern<'arena, str>;

#[derive(Clone, Debug, PartialEq)]
pub enum Ty<'a> {
    Void,
    I1,
    I8,
    I64,
    Ptr(Box<Ty<'a>>),
    Struct(Vec<Ty<'a>>),
    Array(i64, Box<Ty<'a>>),
    // strange redundancy with `FunTy` to avoid extra boxing
    Fun(Vec<Ty<'a>>, Box<Ty<'a>>),
    Named(Tid<'a>),
}

#[derive(Debug)]
pub struct FunTy<'arena> {
    pub params: Vec<Ty<'arena>>,
    pub ret: Ty<'arena>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Operand<'arena> {
    Null,
    Const(i64),
    Gid(Gid<'arena>),
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
    Binop(Bop, Ty<'a>, Operand<'a>, Operand<'a>),
    Alloca(Ty<'a>),
    /// the type of the loaded value and then the operand to load from
    Load(Ty<'a>, Operand<'a>),
    /// the type of the stored value, the value operand to store, and the location to store to
    Store(Ty<'a>, Operand<'a>, Operand<'a>),
    Icmp(Cnd, Ty<'a>, Operand<'a>, Operand<'a>),
    Call(Ty<'a>, Operand<'a>, Vec<(Ty<'a>, Operand<'a>)>),
    Bitcast(Ty<'a>, Operand<'a>, Ty<'a>),
    /// the type pointed to, the value to index from, and the index values
    Gep(Ty<'a>, Operand<'a>, Vec<Operand<'a>>),
}

#[derive(Debug, PartialEq)]
pub enum Terminator<'a> {
    /// return type and optional return value
    /// required if the return type is not void
    Ret(Ty<'a>, Option<Operand<'a>>),
    /// label to branch to
    Br(Lbl<'a>),
    /// the operand to branch on and then the true and false labels
    Cbr(Operand<'a>, Lbl<'a>, Lbl<'a>),
}

#[derive(Debug)]
pub struct Block<'a> {
    pub insns: Vec<(Uid<'a>, Insn<'a>)>,
    pub term: (Uid<'a>, Terminator<'a>),
}

#[derive(Debug)]
pub struct Cfg<'a> {
    pub entry: Block<'a>, 
    pub blocks: Vec<(Lbl<'a>, Block<'a>)>,
}

#[derive(Debug)]
pub struct Fdecl<'a> {
    pub ty: FunTy<'a>,
    pub params: Vec<Uid<'a>>,
    pub cfg: Cfg<'a>,
}

#[derive(Clone, Debug)]
pub enum Ginit<'a> {
    Null,
    Gid(Gid<'a>),
    Int(i64),
    String(String),
    Array(Vec<(Ty<'a>, Ginit<'a>)>),
    Struct(Vec<(Ty<'a>, Ginit<'a>)>),
    Bitcast(Ty<'a>, Box<Ginit<'a>>, Ty<'a>),
}

pub type Gdecl<'a> = (Ty<'a>, Ginit<'a>);

#[derive(Debug)]
pub struct Prog<'a> {
    pub tdecls: HashMap<Tid<'a>, Ty<'a>>,
    pub gdecls: Vec<(Gid<'a>, Gdecl<'a>)>,
    pub fdecls: Vec<(Gid<'a>, Fdecl<'a>)>,
    pub edecls: Vec<(Gid<'a>, Ty<'a>)>,
}
