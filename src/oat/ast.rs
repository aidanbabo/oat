pub struct Range {
    pub start: (usize, usize),
    pub end: (usize, usize),
}

pub struct Node<T> {
    pub t: T,
    pub loc: Range,
}

pub enum Ty {
    Bool,
    Int,
    Ref(Box<Rty>),
}

pub enum Rty {
    String,
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
    And,
    Or,
    IAnd,
    Ior,
    Shl,
    Shr,
    Sar,
}

pub enum Exp {
    Null(Rty),
    Bool(bool),
    Int(i64),
    Str(String),
    Arr(Ty, Vec<Node<Exp>>),
    NewArr(Ty, Box<Node<Exp>>),
    Id(String),
    Index(Box<Node<Exp>>, Box<Node<Exp>>),
    Call(Box<Node<Exp>>, Vec<Node<Exp>>),
    Bop(Binop, Box<Node<Exp>>, Box<Node<Exp>>),
    Uop(Unop, Box<Node<Exp>>),
}

pub struct Field {
    pub id: String,
    pub exp: Node<Exp>,
}

pub struct Vdecl {
    pub id: String,
    pub exp: Node<Exp>,
}

pub type Block = Vec<Node<Stmt>>;

pub enum Stmt {
    Assn(Node<Exp>, Node<Exp>),
    Decl(Vdecl),
    Ret(Option<Node<Exp>>),
    Call(Node<Exp>, Vec<Node<Exp>>),
    If(Node<Exp>, Block, Block),
    For(Vec<Vdecl>, Option<Node<Exp>>, Option<Node<Exp>>, Block),
    While(Node<Exp>, Block),
}

pub struct Gdecl {
    pub name: String,
    pub init: Node<Exp>,
}

pub struct Fdecl {
    pub ret_ty: RetTy,
    pub name: String,
    pub args: Vec<(Ty, String)>,
    pub body: Block,
}

/*
pub struct Field {
    name: String,
    ty: ty,
}
*/

pub enum Decl {
    Var(Node<Gdecl>),
    Fun(Node<Fdecl>),
}

pub type Prog = Vec<Decl>;
