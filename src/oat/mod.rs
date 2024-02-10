use internment::Arena;

use std::ops;
use std::fmt::{self, Debug};

pub mod ast;
mod lexer;
mod parser;
mod ast_to_ll;
mod print;
mod typechecker;

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

pub fn parse<'output>(input: &'_ str, arena: &'output Arena<str>) -> Result<ast::Prog<'output>, Box<dyn std::error::Error>> {
    let mut l = lexer::Lexer::new(input, arena);
    let tokens = l.lex_all()?;
    let prog = parser::Parser::new(tokens).parse_program()?;
    Ok(prog)
}

pub fn typecheck<'ast>(prog: &ast::Prog<'ast>, arena: &'ast Arena<str>) -> Result<typechecker::Context<'ast>, typechecker::TypeError> {
    typechecker::check(prog, arena)
}

// doesn't really need owndership of tcx, but lifetimes are a pain
pub fn to_llvm<'oat, 'll>(oprog: ast::Prog<'oat>, tcx: typechecker::Context<'oat>, ll_arena: &'ll Arena<str>, oat_arena: &'oat Arena<str>) -> llvm::ast::Prog<'ll> {
    let context = ast_to_ll::Context::new(tcx, ll_arena, oat_arena);
    context.lower(oprog)
}

pub use print::write;

pub fn print(prog: &ast::Prog) {
    let _ = write(std::io::stdout().lock(), prog);
}
