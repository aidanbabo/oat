use super::Node;

pub type Ident = String;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ty {
    pub kind: TyKind,
    pub nullable: bool,
}

impl Ty {
    pub fn non_nullable(kind: TyKind) -> Self {
        Self {
            nullable: false,
            kind,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TyKind {
    Void,
    Bool,
    Int,
    String,
    Struct(Ident),
    Array(Box<Ty>),
    Fun(Vec<Ty>, Box<Ty>),
}

impl TyKind {
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
pub enum Exp {
    Null(Ty),
    Bool(bool),
    Int(i64),
    Str(String),
    Id(Ident),
    ArrElems(Ty, Vec<Node<Exp>>),
    ArrLen(Ty, Box<Node<Exp>>),
    // todo: name?
    ArrInit(Ty, Box<Node<Exp>>, Ident, Box<Node<Exp>>),
    Index(Box<Node<Exp>>, Box<Node<Exp>>),
    Length(Box<Node<Exp>>),
    Struct(Ident, Vec<(Ident, Node<Exp>)>),
    Proj(Box<Node<Exp>>, Ident),
    Call(Box<Node<Exp>>, Vec<Node<Exp>>),
    Bop(Binop, Box<Node<Exp>>, Box<Node<Exp>>),
    Uop(Unop, Box<Node<Exp>>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Vdecl {
    pub name: Ident,
    pub exp: Node<Exp>,
}

pub type Block = Vec<Node<Stmt>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Assn(Node<Exp>, Node<Exp>),
    Decl(Vdecl),
    Ret(Option<Node<Exp>>),
    Call(Node<Exp>, Vec<Node<Exp>>),
    If(Node<Exp>, Block, Block),
    IfNull(Ty, Ident, Node<Exp>, Block, Block),
    For(Vec<Vdecl>, Option<Node<Exp>>, Option<Box<Node<Stmt>>>, Block),
    While(Node<Exp>, Block),
}

#[derive(Clone, Debug)]
pub struct Gdecl {
    pub name: Ident,
    pub init: Node<Exp>,
}

#[derive(Clone, Debug)]
pub struct Fdecl {
    pub ret_ty: Ty,
    pub name: String,
    pub args: Vec<(Ty, Ident)>,
    pub body: Block,
}

#[derive(Clone, Debug)]
pub struct Field {
    pub name: Ident,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub struct Tdecl {
    pub name: Ident,
    pub fields: Vec<Field>,
}

#[derive(Clone, Debug)]
pub enum Decl {
    Var(Node<Gdecl>),
    Fun(Node<Fdecl>),
    Type(Node<Tdecl>),
}

pub type Prog = Vec<Decl>;
