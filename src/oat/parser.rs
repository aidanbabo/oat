use super::lexer::{Token, TokenKind};
use super::ast;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError;
pub type ParseResult<T> = Result<T, ParseError>;

// todo: return result
pub fn escape_string(s: &str) -> String {
    let mut out = String::new();
	let mut iter = s.chars();
    while let Some(c) = iter.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }

        let unescaped = iter.next().expect("escaped character");
        let escaped = match unescaped {
            'n' => '\n',
            't' => '\t',
            '\\' => '\\',
            '"' => '"',
            '\'' => '\'', // huh? why would we need to escape this?
            f@'0'..='9' => {
                let s = iter.next().expect("second escaped number");
                let t = iter.next().expect("third escaped number");
                if !matches!((s, t), ('0'..='9', '0'..='9')) {
                    panic!("must be numbers!");
                }
                let zero = '0' as u32;
                let n = (f as u32 - zero) * 100
                    + (s as u32 - zero) * 10
                    + (t as u32 - zero) ;
                if n > 255 {
                    panic!("illegal escaped character constant");
                }
                char::from_u32(n).unwrap()
            }
            c => panic!("unrecocgnized escape character: '{c}'"),
        };
        out.push(escaped);
    }
    out
}

#[derive(Debug)]
pub struct Parser {
    tokens: Vec<Token>,
    next_token: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            next_token: 0,
        }
    }

    fn peek(&mut self) -> Option<&Token> {
        self.tokens.get(self.next_token)
    }

    fn consume(&mut self) -> Option<&Token> {
        let t = self.tokens.get(self.next_token);
        if t.is_some() {
            self.next_token += 1;
        }
        t
    }

    fn test_next_is(&mut self, kind: &TokenKind) -> bool {
        self.peek().is_some_and(|t| &t.kind == kind)
    }

    fn assert_next_is(&mut self, kind: &TokenKind) -> ParseResult<()> {
        if !self.consume().is_some_and(|t| &t.kind == kind) {
            Err(ParseError)
        } else {
            Ok(())
        }
    }

    fn parse_separated<T>(&mut self, mut parse_fn: impl FnMut(&mut Self) -> ParseResult<T>, sep: &TokenKind, end: &TokenKind) -> ParseResult<Vec<T>> {
        let mut v = vec![];

        while !self.test_next_is(end) {
            let t = parse_fn(self)?;
            v.push(t);
            if !self.test_next_is(sep) {
                break;
            }
            self.consume();
        }

        self.assert_next_is(end)?;
        Ok(v)
    }


    pub fn parse_program(&mut self) -> ParseResult<ast::Prog> {
        todo!()
    }

    pub fn parse_stmt(&mut self) -> ParseResult<ast::Stmt> {
        todo!()
    }

    pub fn parse_exp(&mut self) -> ParseResult<ast::Exp> {
        todo!()
    }

    fn parse_any_type(&mut self) -> ParseResult<ast::Ty> {
        let mut t = match self.peek().map(|t| &t.kind) {
            Some(TokenKind::TVoid) => {
                self.consume();
                ast::Ty::non_nullable(ast::TyKind::Void)
            }
            Some(TokenKind::TBool) => {
                self.consume();
                ast::Ty::non_nullable(ast::TyKind::Bool)
            }
            Some(TokenKind::TInt) => {
                self.consume();
                ast::Ty::non_nullable(ast::TyKind::Int)
            }
            Some(TokenKind::TString) => {
                self.consume();
                ast::Ty::non_nullable(ast::TyKind::String)
            }
            Some(TokenKind::UIdent(ty_name)) => {
                let ty_name = ty_name.clone();
                self.consume();
                ast::Ty::non_nullable(ast::TyKind::Struct(ty_name))
            }
            Some(TokenKind::LParen) => {
                self.consume();
                let mut arg_types = self.parse_separated(Self::parse_type, &TokenKind::Comma, &TokenKind::RParen)?;
                // todo: hack for parenthesized types, would still parse '(int,)' as 'int' even though it is
                // invalid as a both parenthesized type and function type
                if arg_types.len() == 1 && !self.test_next_is(&TokenKind::Arrow) {
                    arg_types.pop().unwrap()
                } else {
                    self.assert_next_is(&TokenKind::Arrow)?;
                    let ret_ty = self.parse_ret_type()?;
                    ast::Ty::non_nullable(ast::TyKind::Fun(arg_types, Box::new(ret_ty)))
                }
            }
            None => return Err(ParseError),
            k => unimplemented!("unexpected token kind: {k:?}"),
        };

        loop {
            match self.peek().map(|t| &t.kind) {
                Some(TokenKind::Question) => {
                    self.consume();
                    if !t.kind.is_ref() {
                        panic!("not a ref type");
                    }
                    if t.nullable {
                        panic!("can't make a nullable type nullable as it is not a reference type")
                    }
                    t.nullable = true;
                }
                Some(TokenKind::LBracket) => {
                    self.consume();
                    self.assert_next_is(&TokenKind::RBracket)?;
                    t = ast::Ty {
                        nullable: false,
                        kind: ast::TyKind::Array(Box::new(t)),
                    };
                }
                _ => break,
            }
        }
        Ok(t)
    }

    fn parse_type(&mut self) -> ParseResult<ast::Ty> {
        let ty = self.parse_any_type()?;
        if ty.kind == ast::TyKind::Void {
            return Err(ParseError);
        }
        Ok(ty)
    }

    fn parse_ref_type(&mut self) -> ParseResult<ast::Ty> {
        let ty = self.parse_any_type()?;
        if !ty.kind.is_ref() {
            return Err(ParseError);
        }
        Ok(ty)
    }

    fn parse_ret_type(&mut self) -> ParseResult<ast::Ty> {
        self.parse_any_type()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // todo: not very good unit tests tbh
    // stop relying on lexer
    #[test]
    fn parse_type() {
        let tokens = crate::oat::lexer::Lexer::new("(()->int[]?)?").lex_all();
        let mut p = Parser::new(tokens);
        let ty = p.parse_type();
        let expected = ast::Ty {
            nullable: true,
            kind: ast::TyKind::Fun(
                vec![],
                Box::new(ast::Ty {
                    nullable: true,
                    kind: ast::TyKind::Array(
                        Box::new(ast::Ty {
                            nullable: false,
                            kind: ast::TyKind::Int,
                        })
                    ),
                }),
            ),
        };
        assert_eq!(ty, Ok(expected))
    }
}
