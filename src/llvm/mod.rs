// CHANGES:
//      load: type is the type being loaded not the type being loaded from
//      gep: type is not the pointer type but the type listed after the `getelementptr` keyword.

use internment::{Arena, ArenaIntern};

pub mod ast;
pub mod dataflow;
mod interp;
mod print;

// todo: priv
pub mod lexer;
pub mod parser;

pub use interp::ExecError;

pub fn parse<'ast>(input: &str, arena: &'ast Arena<str>) -> Result<ast::Prog<'ast>, parser::ParseError> {
    parser::parse(input, arena)
}

pub fn interp(prog: &ast::Prog, args: &[&str], entry: ArenaIntern<'_, str>) -> Result<u8, ExecError> {
    interp::interp_prog(prog, args, entry).map(|i| i as u8)
}

pub use print::write;

pub fn print(prog: &ast::Prog) {
    let _ = write(std::io::stdout().lock(), prog);
}
