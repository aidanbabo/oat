// CHANGES:
//      load: type is the type being loaded not the type being loaded from
//      gep: type is not the pointer type but the type listed after the `getelementptr` keyword.

use internment::Arena;

pub mod ast;
pub mod dataflow;
mod interp;
mod print;
pub mod utils;

// todo: priv
pub mod lexer;
pub mod parser;

pub use interp::ExecError;

use crate::StrInterner;

#[derive(Default)]
pub struct Interners {
    pub labels: StrInterner<ast::Lbl>,
    pub types: StrInterner<ast::Tid>,
    pub globals: StrInterner<ast::Gid>,
}

pub fn parse<'ast>(input: &str, arena: &'ast Arena<str>) -> Result<ast::Prog<'ast>, parser::ParseError> {
    parser::parse(input, arena)
}

pub fn interp(prog: &ast::Prog, args: &[&str], entry: &str) -> Result<u8, ExecError> {
    let entry_id = prog
        .tables
        .globals
        .iter()
        .position(|s| &**s == entry)
        .expect("valid entry point") as u32;
    interp::interp_prog(prog, args, entry_id.into()).map(|i| i as u8)
}

pub use print::write;

pub fn print(prog: &ast::Prog) {
    let _ = write(std::io::stdout().lock(), prog);
}
