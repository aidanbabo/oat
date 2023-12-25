/// Row column pairs
pub struct Range {
    pub start: (usize, usize),
    pub end: (usize, usize),
}

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

pub enum Ty {
    Bool,
    Int,
    Ref(Box<RefTy>),
    NullRef(Box<RefTy>),
}

pub enum RefTy {
    String,
    Struct(Ident),
    Array(Ty),
    Fun(Vec<Ty>, Box<RetTy>),
}

pub enum RetTy {
    Void,
    Val(Ty),
}

pub enum Unop {
    Neg,
    Lognot,
    Bitnot,
}

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

pub enum Expr {
    Null(RefTy),
    Bool(bool),
    Int(i64),
    Str(String),
    Id(Ident),
    ArrElems(Ty, Vec<Node<Expr>>),
    ArrLen(Ty, Box<Node<Expr>>),
    // todo: name?
    ArrInit(Ty, Box<Node<Expr>>, Ident, Box<Node<Expr>>),
    Index(Box<Node<Expr>>, Box<Node<Expr>>),
    Length(Box<Node<Expr>>),
    Struct(Ident, Vec<(Ident, Node<Expr>)>),
    Proj(Box<Node<Expr>>, Ident),
    Call(Box<Node<Expr>>, Vec<Node<Expr>>),
    Bop(Binop, Box<Node<Expr>>, Box<Node<Expr>>),
    Uop(Unop, Box<Node<Expr>>),
}

pub struct Vdecl {
    pub name: Ident,
    pub expr: Node<Expr>,
}

pub type Block = Vec<Node<Stmt>>;

pub enum Stmt {
    Assn(Node<Expr>, Node<Expr>),
    Decl(Vdecl),
    Ret(Option<Node<Expr>>),
    Call(Node<Expr>, Vec<Node<Expr>>),
    If(Node<Expr>, Block, Block),
    IfNull(RefTy, Ident, Box<Node<Expr>>, Block, Block),
    For(Vec<Vdecl>, Option<Node<Expr>>, Option<Box<Node<Stmt>>>, Block),
    While(Node<Expr>, Block),
}

pub struct Gdecl {
    pub name: Ident,
    pub init: Node<Expr>,
}

pub struct Fdecl {
    pub ret_ty: RetTy,
    pub name: String,
    pub args: Vec<(Ty, Ident)>,
    pub body: Block,
}

pub struct Field {
    pub name: Ident,
    pub ty: Ty,
}

pub struct Tdecl {
    pub name: Ident,
    pub fields: Vec<Field>,
}

pub enum Decl {
    Var(Node<Gdecl>),
    Fun(Node<Fdecl>),
    Type(Node<Tdecl>),
}

pub type Prog = Vec<Decl>;
