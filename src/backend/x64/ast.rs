#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[repr(transparent)]
pub struct Label(u32);

impl Label {
    pub fn ix(self) -> usize {
        self.0 as usize
    }
}

impl From<u32> for Label {
    fn from(value: u32) -> Self {
        Label(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Imm {
    Word(i64),
    Lbl(Label),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Imm(Imm),
    Reg(Reg),
    Ind1(Imm),
    Ind2(Reg),
    Ind3(Imm, Reg),
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
pub enum Insn {
    Neg(Op), // Reg?
    Add(Op, Op),
    Sub(Op, Op),
    Imul(Op, Reg),
    Inc(Op),
    Dec(Op),
    Not(Op),
    And(Op, Op),
    Or(Op, Op),
    Xor(Op, Op),
    Sar(Op, Op),
    Shl(Op, Op),
    Shr(Op, Op),
    Set(Cond, Op),
    /// Ind, op
    Lea(Op, Op),
    /// src -> dest
    Mov(Op, Op),
    Push(Op),
    Pop(Op),
    Cmp(Op, Op),
    Jmp(Op),
    Ret,
    J(Cond, Op),
    Call(Op),
}

#[derive(Debug)]
pub struct CodeBlock {
    pub global: bool,
    pub label: Label,
    pub insns: Vec<Insn>,
}

#[derive(Debug)]
pub enum Data {
    Quad(Imm),
    String(String),
}

#[derive(Debug)]
pub struct DataBlock {
    pub global: bool,
    pub label: Label,
    pub data: Vec<Data>,
}

#[derive(Debug)]
pub struct Prog {
    pub code: Vec<CodeBlock>,
    pub data: Vec<DataBlock>,
    pub labels: Vec<Box<str>>,
}
