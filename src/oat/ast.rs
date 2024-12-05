use internment::ArenaIntern;

use super::Node;

pub type Ident<'ast> = ArenaIntern<'ast, str>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ty<'ast> {
    pub kind: TyKind<'ast>,
    pub nullable: bool,
}

impl<'ast> Ty<'ast> {
    pub fn non_nullable(kind: TyKind<'ast>) -> Self {
        Self {
            nullable: false,
            kind,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TyKind<'ast> {
    Void,
    Bool,
    Int,
    String,
    Struct(Ident<'ast>),
    Array(Box<Ty<'ast>>),
    Fun(Vec<Ty<'ast>>, Box<Ty<'ast>>),
}

impl TyKind<'_> {
    pub fn is_ref(&self) -> bool {
        use TyKind as Tk;
        matches!(self, Tk::String | Tk::Struct(..) | Tk::Array(..) | Tk::Fun(..))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Unop {
    Neg,
    LogNot,
    BitNot,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    IAnd,
    IOr,
    Shl,
    Shr,
    Sar,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Exp<'ast> {
    Null(Ty<'ast>),
    Bool(bool),
    Int(i64),
    Str(ArenaIntern<'ast, str>),
    Id(Ident<'ast>),
    ArrElems(Ty<'ast>, Vec<Node<Exp<'ast>>>),
    ArrLen(Ty<'ast>, Box<Node<Exp<'ast>>>),
    // todo: name?
    ArrInit(Ty<'ast>, Box<Node<Exp<'ast>>>, Ident<'ast>, Box<Node<Exp<'ast>>>),
    Index(Box<Node<Exp<'ast>>>, Box<Node<Exp<'ast>>>),
    Length(Box<Node<Exp<'ast>>>),
    Struct(Ident<'ast>, Vec<(Ident<'ast>, Node<Exp<'ast>>)>),
    Proj(Box<Node<Exp<'ast>>>, Ident<'ast>),
    Call(Box<Node<Exp<'ast>>>, Vec<Node<Exp<'ast>>>),
    Bop(Binop, Box<Node<Exp<'ast>>>, Box<Node<Exp<'ast>>>),
    Uop(Unop, Box<Node<Exp<'ast>>>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Vdecl<'ast> {
    pub name: Ident<'ast>,
    pub exp: Node<Exp<'ast>>,
}

pub type Block<'ast> = Vec<Node<Stmt<'ast>>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt<'ast> {
    Assn(Node<Exp<'ast>>, Node<Exp<'ast>>),
    Decl(Vdecl<'ast>),
    Ret(Option<Node<Exp<'ast>>>),
    Call(Node<Exp<'ast>>, Vec<Node<Exp<'ast>>>),
    If(Node<Exp<'ast>>, Block<'ast>, Block<'ast>),
    IfNull(Ty<'ast>, Ident<'ast>, Node<Exp<'ast>>, Block<'ast>, Block<'ast>),
    For(Vec<Vdecl<'ast>>, Option<Node<Exp<'ast>>>, Option<Box<Node<Stmt<'ast>>>>, Block<'ast>),
    While(Node<Exp<'ast>>, Block<'ast>),
}

#[derive(Clone, Debug)]
pub struct Gdecl<'ast> {
    pub name: Ident<'ast>,
    pub init: Node<Exp<'ast>>,
}

#[derive(Clone, Debug)]
pub struct Fdecl<'ast> {
    pub ret_ty: Ty<'ast>,
    pub name: Ident<'ast>,
    pub args: Vec<(Ty<'ast>, Ident<'ast>)>,
    pub body: Block<'ast>,
}

#[derive(Clone, Debug)]
pub struct Field<'ast> {
    pub name: Ident<'ast>,
    pub ty: Ty<'ast>,
}

#[derive(Clone, Debug)]
pub struct Tdecl<'ast> {
    pub name: Ident<'ast>,
    pub fields: Vec<Field<'ast>>,
}

#[derive(Clone, Debug)]
pub enum Decl<'ast> {
    Var(Node<Gdecl<'ast>>),
    Fun(Node<Fdecl<'ast>>),
    Type(Node<Tdecl<'ast>>),
}

pub type Prog<'ast> = Vec<Decl<'ast>>;
