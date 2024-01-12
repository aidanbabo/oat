pub mod ast;
mod lexer;
mod parser;

pub fn parse(input: &str) -> Result<ast::Prog, ()> {
    let mut l = lexer::Lexer::new(input);
    let tokens = l.lex_all();
    for t in &tokens {
        println!("{t:?}");
    }
    Err(())
}
