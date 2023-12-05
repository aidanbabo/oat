use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parser, "/oat/parser.rs"); // synthesized by LALRPOP
pub mod ast;
mod parser_utils;

pub type ParseError<'a> = lalrpop_util::ParseError<usize, lalrpop_util::lexer::Token<'a>, &'static str>;
pub type ParseResult<'a, T> = Result<T, ParseError<'a>>;

pub fn parse(input: &str) -> ParseResult<ast::Prog> {
    parser::ProgParser::new().parse(input)
}
