// CHANGES:
//      load: type is the type being loaded not the type being loaded from
//      gep: type is not the pointer type but the type listed after the `getelementptr` keyword.

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parser, "/llvm/parser.rs"); // synthesized by LALRPOP
pub mod ast;
pub(crate) mod parser_utils;
mod interp;
mod print;

pub use interp::ExecError;

pub type ParseError<'a> = lalrpop_util::ParseError<usize, lalrpop_util::lexer::Token<'a>, &'static str>;
pub type ParseResult<'a, T> = Result<T, ParseError<'a>>;

pub fn parse(input: &str) -> ParseResult<ast::Prog> {
    parser::ProgParser::new().parse(input)
}

pub fn interp(prog: &ast::Prog, args: &[&str]) -> Result<i64, ExecError> {
    interp::interp_prog(prog, args)
}

pub fn print(prog: &ast::Prog) {
    print::print(prog)
}

