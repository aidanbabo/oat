use lalrpop_util::lalrpop_mod;
use std::fmt;

lalrpop_mod!(parser, "/llvm/parser.rs"); // synthesized by LALRPOP
pub mod ast;
pub(crate) mod parser_utils;
mod interp;

pub use interp::ExecError;

pub type ParseError<'a> = lalrpop_util::ParseError<usize, lalrpop_util::lexer::Token<'a>, &'static str>;
pub type ParseResult<'a, T> = Result<T, ParseError<'a>>;

pub fn parse(input: &str) -> ParseResult<ast::Prog> {
    parser::ProgParser::new().parse(input)
}

pub fn interp(prog: &ast::Prog, args: &[&str]) -> Result<i64, ExecError> {
    interp::interp_prog(prog, args)
}

fn write_separated<T, W>(f: &mut W, sep: &str, ts: impl IntoIterator<Item = T>) -> fmt::Result
    where T: fmt::Display,
          W: fmt::Write,
{
    let mut first = true;
    for t in ts {
        if first {
            write!(f, "{t}")?
        } else {
            write!(f, "{sep}{t}")?
        }
        first = false;
    }
    Ok(())
}
