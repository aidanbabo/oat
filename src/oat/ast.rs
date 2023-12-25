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
    LogNot,
    BitNot,
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

pub enum Exp {
    Null(RefTy),
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

pub struct Vdecl {
    pub name: Ident,
    pub exp: Node<Exp>,
}

pub type Block = Vec<Node<Stmt>>;

pub enum Stmt {
    Assn(Node<Exp>, Node<Exp>),
    Decl(Vdecl),
    Ret(Option<Node<Exp>>),
    Call(Node<Exp>, Vec<Node<Exp>>),
    If(Node<Exp>, Block, Block),
    IfNull(RefTy, Ident, Box<Node<Exp>>, Block, Block),
    For(Vec<Vdecl>, Option<Node<Exp>>, Option<Box<Node<Stmt>>>, Block),
    While(Node<Exp>, Block),
}

pub struct Gdecl {
    pub name: Ident,
    pub init: Node<Exp>,
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
