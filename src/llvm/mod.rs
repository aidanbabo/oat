use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parser, "/llvm/parser.rs"); // synthesized by LALRPOP
pub mod ast;
pub(crate) mod parser_utils;
mod interp;

pub type ParseError<'a> = lalrpop_util::ParseError<usize, lalrpop_util::lexer::Token<'a>, &'static str>;
pub type ParseResult<'a, T> = Result<T, ParseError<'a>>;

pub fn parse(input: &str) -> ParseResult<ast::Prog> {
    parser::ProgParser::new().parse(input)
}

