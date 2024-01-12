use super::{ast, Range, Node};
use super::lexer::{Token, TokenKind, TokenData};

use enum_map::{EnumMap, enum_map};
use once_cell::sync::Lazy;

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

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    // nothing!
    None,
    // [\]
    IOr,
    // [&]
    IAnd,
    // |
    Or,
    // &
    And,
    /// == !=
    Equality,
    /// > < >= <=
    Comparison,
    /// >> << <<<
    Bitshift,
    /// + -
    Term,
    /// *
    Factor,
    /// ! -
    Unary,
    /// . ()
    Call,
}

impl Precedence {
    pub fn next(self) -> Self {
        use Precedence::*;
        match self {
            None => IOr,
            IOr => IAnd,
            IAnd => Or,
            Or => And,
            And => Equality,
            Equality => Comparison,
            Comparison => Bitshift,
            Bitshift => Term,
            Term => Factor,
            Factor => Unary,
            Unary => Call,
            Call => unreachable!(),
        }
    }
}


type InfixParseFn = fn(&mut Parser, Node<ast::Exp>) -> ParseResult<Node<ast::Exp>>;
type PrefixParseFn = fn(&mut Parser) -> ParseResult<Node<ast::Exp>>;

#[derive(Clone, Copy)]
struct ParseRule {
    precedence: Precedence,
    prefix: Option<PrefixParseFn>,
    infix: Option<InfixParseFn>,
}

impl ParseRule {
    pub const fn new(precedence: Precedence, prefix: Option<PrefixParseFn>, infix: Option<InfixParseFn>) -> Self {
        ParseRule { precedence, prefix, infix }
    }
}

fn get_rule(kind: TokenKind) -> ParseRule {
    static PARSE_RULES: Lazy<EnumMap<TokenKind, ParseRule>> = Lazy::new(||{ 
        enum_map! { 
            TokenKind::IntLit => ParseRule::new(Precedence::None, Some(Parser::parse_int_lit), None),
            TokenKind::Null => ParseRule::new(Precedence::None, None, None),
            TokenKind::String => ParseRule::new(Precedence::None, None, None),
            TokenKind::Ident => ParseRule::new(Precedence::None, None, None),
            TokenKind::UIdent => ParseRule::new(Precedence::None, None, None),
            TokenKind::TInt => ParseRule::new(Precedence::None, None, None),
            TokenKind::TVoid => ParseRule::new(Precedence::None, None, None),
            TokenKind::TString => ParseRule::new(Precedence::None, None, None),
            TokenKind::If => ParseRule::new(Precedence::None, None, None),
            TokenKind::Ifq => ParseRule::new(Precedence::None, None, None),
            TokenKind::Else => ParseRule::new(Precedence::None, None, None),
            TokenKind::While => ParseRule::new(Precedence::None, None, None),
            TokenKind::Return => ParseRule::new(Precedence::None, None, None),
            TokenKind::Var => ParseRule::new(Precedence::None, None, None),
            TokenKind::Struct => ParseRule::new(Precedence::None, None, None),
            TokenKind::Semi => ParseRule::new(Precedence::None, None, None),
            TokenKind::Comma => ParseRule::new(Precedence::None, None, None),
            TokenKind::LBrace => ParseRule::new(Precedence::None, None, None),
            TokenKind::RBrace => ParseRule::new(Precedence::None, None, None),
            TokenKind::Plus => ParseRule::new(Precedence::Term, None, Some(Parser::parse_binary)),
            TokenKind::Dash => ParseRule::new(Precedence::Term, Some(Parser::parse_unary), Some(Parser::parse_binary)),
            TokenKind::Star => ParseRule::new(Precedence::Factor, None, Some(Parser::parse_binary)),
            TokenKind::EqEq => ParseRule::new(Precedence::Equality, None, Some(Parser::parse_binary)),
            TokenKind::Eq => ParseRule::new(Precedence::None, None, None),
            TokenKind::LParen => ParseRule::new(Precedence::None, None, None),
            TokenKind::RParen => ParseRule::new(Precedence::None, None, None),
            TokenKind::LBracket => ParseRule::new(Precedence::None, None, None),
            TokenKind::RBracket => ParseRule::new(Precedence::None, None, None),
            TokenKind::Tilde => ParseRule::new(Precedence::None, Some(Parser::parse_unary), None),
            TokenKind::Bang => ParseRule::new(Precedence::None, Some(Parser::parse_unary), None),
            TokenKind::Global => ParseRule::new(Precedence::None, None, None),
            TokenKind::For => ParseRule::new(Precedence::None, None, None),
            TokenKind::TBool => ParseRule::new(Precedence::None, None, None),
            TokenKind::Length => ParseRule::new(Precedence::None, None, None),
            TokenKind::True => ParseRule::new(Precedence::None, None, None),
            TokenKind::False => ParseRule::new(Precedence::None, None, None),
            TokenKind::Dot => ParseRule::new(Precedence::None, None, None),
            TokenKind::New => ParseRule::new(Precedence::None, None, None),
            TokenKind::Gt => ParseRule::new(Precedence::Comparison, None, Some(Parser::parse_binary)),
            TokenKind::GtEq => ParseRule::new(Precedence::Comparison, None, Some(Parser::parse_binary)),
            TokenKind::Lt => ParseRule::new(Precedence::Comparison, None, Some(Parser::parse_binary)),
            TokenKind::LtEq => ParseRule::new(Precedence::Comparison, None, Some(Parser::parse_binary)),
            TokenKind::BangEq => ParseRule::new(Precedence::Equality, None, Some(Parser::parse_binary)),
            TokenKind::Bar => ParseRule::new(Precedence::Or, None, Some(Parser::parse_binary)),
            TokenKind::Amper => ParseRule::new(Precedence::And, None, Some(Parser::parse_binary)),
            TokenKind::IOr => ParseRule::new(Precedence::IOr, None, Some(Parser::parse_binary)),
            TokenKind::IAnd => ParseRule::new(Precedence::IAnd, None, Some(Parser::parse_binary)),
            TokenKind::LtLt => ParseRule::new(Precedence::Bitshift, None, Some(Parser::parse_binary)),
            TokenKind::GtGt => ParseRule::new(Precedence::Bitshift, None, Some(Parser::parse_binary)),
            TokenKind::GtGtGt => ParseRule::new(Precedence::Bitshift, None, Some(Parser::parse_binary)),
            TokenKind::Arrow => ParseRule::new(Precedence::None, None, None),
            TokenKind::Question => ParseRule::new(Precedence::None, None, None),
        }
    });

    PARSE_RULES[kind]
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

    pub fn parse_exp(&mut self) -> ParseResult<Node<ast::Exp>> {
        self.parse_precedence(Precedence::IOr)
    }

    fn parse_precedence(&mut self, precedence: Precedence) -> ParseResult<Node<ast::Exp>> {
        let rule = self.peek().map(|t| get_rule(t.kind).prefix).flatten();
        let Some(prefix) = rule else {
            panic!("expected expression")
        };

        let mut lhs = prefix(self)?;

        loop {
            let next_rule = self.peek().map(|t| get_rule(t.kind));
            let Some(rule) = next_rule else { break };
            if precedence > rule.precedence {
                break;
            }

            let infix = next_rule.map(|r| r.infix).flatten();
            if let Some(infix) = infix {
                lhs = infix(self, lhs)?;
            } else {
                // unreachable?
                panic!("expected infix rule fr!")
            }
        }

        Ok(lhs)
    }

    fn parse_int_lit(&mut self) -> ParseResult<Node<ast::Exp>> {
        let int_lit = self.consume().unwrap();
        let TokenData::Int(val) = int_lit.data else { unreachable!() };
        Ok(Node { loc: int_lit.loc, t: ast::Exp::Int(val) })
    }

    fn parse_unary(&mut self) -> ParseResult<Node<ast::Exp>> {
        let unop_token = self.consume().unwrap().clone();

        let exp = self.parse_precedence(Precedence::Unary)?;
        let unop = match unop_token.kind {
            TokenKind::Dash => ast::Unop::Neg,
            TokenKind::Bang => ast::Unop::LogNot,
            TokenKind::Tilde => ast::Unop::BitNot,
            _ => unreachable!(),
        };

        let loc = Range::merge(unop_token.loc, exp.loc);
        Ok(Node { loc, t: ast::Exp::Uop(unop, Box::new(exp)) })
    }

    fn parse_binary(&mut self, lhs: Node<ast::Exp>) -> ParseResult<Node<ast::Exp>> {
        let binop_kind = self.consume().unwrap().kind;
        let rule = get_rule(binop_kind);
        let rhs = self.parse_precedence(rule.precedence.next())?;
        // todo: move to previous function?
        let binop = match binop_kind {
            TokenKind::IOr => ast::Binop::IOr,
            TokenKind::IAnd => ast::Binop::IAnd,
            TokenKind::Bar => ast::Binop::Or,
            TokenKind::Amper => ast::Binop::And,
            TokenKind::Plus => ast::Binop::Add,
            TokenKind::Dash => ast::Binop::Sub,
            TokenKind::Star => ast::Binop::Mul,
            TokenKind::EqEq => ast::Binop::Eq,
            TokenKind::BangEq => ast::Binop::Neq,
            TokenKind::Gt => ast::Binop::Gt,
            TokenKind::Lt => ast::Binop::Lt,
            TokenKind::GtEq => ast::Binop::Gte,
            TokenKind::LtEq => ast::Binop::Lte,
            TokenKind::LtLt => ast::Binop::Shl,
            TokenKind::GtGt => ast::Binop::Shr,
            TokenKind::GtGtGt => ast::Binop::Sar,
            _ => unreachable!(),
        };
        let loc = Range::merge(lhs.loc, rhs.loc);
        Ok(Node { loc, t: ast::Exp::Bop(binop, Box::new(lhs), Box::new(rhs)) })
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
            Some(TokenKind::UIdent) => {
                let t = self.consume().unwrap();
                let TokenData::String(name) = &t.data else { unreachable!() };
                ast::Ty::non_nullable(ast::TyKind::Struct(name.clone()))
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
    
    #[test]
    fn parse_exp() {
        let tokens = crate::oat::lexer::Lexer::new("5+6*7+8").lex_all();
        let mut p = Parser::new(tokens);
        let e = p.parse_exp();
        let expected = Node::no_loc(ast::Exp::Bop(ast::Binop::Add, 
            Box::new(Node::no_loc(ast::Exp::Bop(ast::Binop::Add, 
                Box::new(Node::no_loc(ast::Exp::Int(5))),
                Box::new(Node::no_loc(ast::Exp::Bop(ast::Binop::Mul,
                    Box::new(Node::no_loc(ast::Exp::Int(6))),
                    Box::new(Node::no_loc(ast::Exp::Int(7))),
                ))),
            ))),
            Box::new(Node::no_loc(ast::Exp::Int(8)))
        ));
        assert_eq!(e, Ok(expected));
    }
}
