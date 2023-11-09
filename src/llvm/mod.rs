use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parser, "/llvm/parser.rs"); // synthesized by LALRPOP
pub mod ast;
pub(crate) mod parser_utils;

pub fn parse(input: &str) -> ast::Prog {
    parser::ProgParser::new().parse(input).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[skip]
    #[test]
    fn llvm() {
        assert!(parser::TermParser::new().parse("22").is_ok());
        assert!(parser::TermParser::new().parse("(22)").is_ok());
        assert!(parser::TermParser::new().parse("((((22))))").is_ok());
        assert!(parser::TermParser::new().parse("((22)").is_err());
    }
}
