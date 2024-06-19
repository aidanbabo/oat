use internment::ArenaIntern;

pub type Label<'arena> = ArenaIntern<'arena, str>;

#[derive(Clone, Copy, Debug)]
pub enum Reg {
    Rax,
    Rbx,
    Rcx,
    Rdx,
    Rsi,
    Rdi,
    Rbp,
    Rsp,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
    Rip,
}

#[derive(Clone, Copy, Debug)]
pub enum Imm<'asm> {
    Word(i64),
    Lbl(Label<'asm>),
}

#[derive(Clone, Copy, Debug)]
pub enum Op<'asm> {
    Imm(Imm<'asm>),
    Reg(Reg),
    Ind1(Imm<'asm>),
    Ind2(Reg),
    Ind3(Imm<'asm>, Reg),
}

#[derive(Clone, Copy, Debug)]
pub enum Cond {
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
}

/// at&t :(
#[derive(Clone, Copy, Debug)]
pub enum Insn<'asm> {
    Neg(Op<'asm>), // Reg?
    Add(Op<'asm>, Op<'asm>),
    Sub(Op<'asm>, Op<'asm>),
    Imul(Op<'asm>, Reg),
    Inc(Op<'asm>),
    Dec(Op<'asm>),
    Not(Op<'asm>),
    And(Op<'asm>, Op<'asm>),
    Or(Op<'asm>, Op<'asm>),
    Xor(Op<'asm>, Op<'asm>),
    Sar(Op<'asm>, Op<'asm>),
    Shl(Op<'asm>, Op<'asm>),
    Shr(Op<'asm>, Op<'asm>),
    Set(Cond, Op<'asm>),
    /// Ind, op
    Lea(Op<'asm>, Op<'asm>),
    /// src -> dest
    Mov(Op<'asm>, Op<'asm>),
    Push(Op<'asm>),
    Pop(Op<'asm>),
    Cmp(Op<'asm>, Op<'asm>),
    Jmp(Op<'asm>),
    Ret,
    J(Cond, Op<'asm>),
    Call(Op<'asm>),
}

#[derive(Debug)]
pub struct CodeBlock<'asm> {
    pub global: bool,
    pub label: Label<'asm>,
    pub insns: Vec<Insn<'asm>>,
}

#[derive(Debug)]
pub enum Data<'asm> {
    Quad(Imm<'asm>),
    String(String),
}

#[derive(Debug)]
pub struct DataBlock<'asm> {
    pub global: bool,
    pub label: Label<'asm>,
    pub data: Vec<Data<'asm>>,
}

#[derive(Debug)]
pub struct Prog<'asm> {
    pub code: Vec<CodeBlock<'asm>>,
    pub data: Vec<DataBlock<'asm>>,
}
