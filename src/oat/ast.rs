/// Row column pairs
#[derive(Debug)]
pub struct Range {
    pub start: (usize, usize),
    pub end: (usize, usize),
}

#[derive(Debug)]
pub struct Node<T> {
    pub t: T,
    pub loc: Range,
}

impl<T> Node<T> {
    pub fn no_loc(t: T) -> Self {
        Node {
            loc: Range {
                start: (0, 0),
                end: (0, 0),
            },
            t,
        }
    }
}

pub type Ident = String;

#[derive(Debug, PartialEq, Eq)]
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

#[derive(Debug, PartialEq, Eq)]
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

#[derive(Debug)]
pub enum Unop {
    Neg,
    LogNot,
    BitNot,
}

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
pub struct Vdecl {
    pub name: Ident,
    pub exp: Node<Exp>,
}

pub type Block = Vec<Node<Stmt>>;

#[derive(Debug)]
pub enum Stmt {
    Assn(Node<Exp>, Node<Exp>),
    Decl(Vdecl),
    Ret(Option<Node<Exp>>),
    Call(Node<Exp>, Vec<Node<Exp>>),
    If(Node<Exp>, Block, Block),
    IfNull(Ty, Ident, Box<Node<Exp>>, Block, Block),
    For(Vec<Vdecl>, Option<Node<Exp>>, Option<Box<Node<Stmt>>>, Block),
    While(Node<Exp>, Block),
}

#[derive(Debug)]
pub struct Gdecl {
    pub name: Ident,
    pub init: Node<Exp>,
}

#[derive(Debug)]
pub struct Fdecl {
    pub ret_ty: Ty,
    pub name: String,
    pub args: Vec<(Ty, Ident)>,
    pub body: Block,
}

#[derive(Debug)]
pub struct Field {
    pub name: Ident,
    pub ty: Ty,
}

#[derive(Debug)]
pub struct Tdecl {
    pub name: Ident,
    pub fields: Vec<Field>,
}

#[derive(Debug)]
pub enum Decl {
    Var(Node<Gdecl>),
    Fun(Node<Fdecl>),
    Type(Node<Tdecl>),
}

pub type Prog = Vec<Decl>;
