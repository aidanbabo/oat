use std::ops;
use std::fmt::{self, Debug};

pub mod ast;
mod lexer;
mod parser;
mod ast_to_ll;
mod print;

use crate::llvm;


/// Row-column pairs
#[derive(Copy, Clone, Debug)]
pub struct Range {
    pub start: (usize, usize),
    pub end: (usize, usize),
}

impl Range {
    pub fn merge(l: Range, r: Range) -> Range {
        Range {
            start: l.start,
            end: r.end,
        }
    }
}

#[derive(Clone)]
pub struct Node<T> {
    pub t: T,
    pub loc: Range,
}

impl<T: Debug> fmt::Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.t)
    }
}

impl<T> Node<T> {
    pub fn no_loc(t: T) -> Self {
        Node {
            loc: Range {
                start: (0, 0),
                end: (0, 0),
            },
            t,
        }
    }
}

impl<T> ops::Deref for Node<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.t
    }
}

impl<T: PartialEq> PartialEq for Node<T> {
    fn eq(&self, other: &Self) -> bool {
        self.t == other.t
    }
}

pub fn parse(input: &str) -> Result<ast::Prog, Box<dyn std::error::Error>> {
    let mut l = lexer::Lexer::new(input);
    let tokens = l.lex_all();
    let prog = parser::Parser::new(tokens).parse_program()?;
    Ok(prog)
}

pub fn to_llvm(oprog: ast::Prog) -> llvm::ast::Prog {
    let context = ast_to_ll::Context::new();

    context.lower(oprog)
}

pub use print::write;

pub fn print(prog: &ast::Prog) {
    let _ = write(std::io::stdout().lock(), prog);
}
