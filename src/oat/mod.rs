use std::ops;

pub mod ast;
mod lexer;
mod parser;


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

#[derive(Clone, Debug)]
pub struct Node<T> {
    pub t: T,
    pub loc: Range,
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

pub fn parse(input: &str) -> Result<ast::Prog, ()> {
    let mut l = lexer::Lexer::new(input);
    let tokens = l.lex_all();
    for t in &tokens {
        println!("{t:?}");
    }
    let stmt = parser::Parser::new(tokens).parse_stmt().unwrap();
    let prog = vec![ast::Decl::Fun(Node::no_loc(ast::Fdecl { ret_ty: ast::Ty { nullable: false, kind: ast::TyKind::Void }, name: "program".to_string(), args: vec![], body: vec![stmt] }))];
    Ok(prog)
}

