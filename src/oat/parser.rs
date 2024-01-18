use super::{ast, Range, Node};
use super::lexer::{Token, TokenKind, TokenData};

use std::fmt;

use enum_map::{EnumMap, enum_map};
use once_cell::sync::Lazy;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError;
impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "parse error")
    }
}
impl std::error::Error for ParseError {}

pub type ParseResult<T> = Result<T, ParseError>;

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
    /// []
    Index,
    /// .
    Proj,
    /// ()
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
            Unary => Index,
            Index => Proj,
            Proj => Call,
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
            TokenKind::String => ParseRule::new(Precedence::None, Some(Parser::parse_string_lit), None),
            TokenKind::Ident => ParseRule::new(Precedence::None, Some(Parser::parse_ident), None),
            TokenKind::UIdent => ParseRule::new(Precedence::None, None, None),
            TokenKind::TInt => ParseRule::new(Precedence::None, Some(Parser::parse_null_ptr), None),
            TokenKind::TVoid => ParseRule::new(Precedence::None, Some(Parser::parse_null_ptr), None),
            TokenKind::TString => ParseRule::new(Precedence::None, Some(Parser::parse_null_ptr), None),
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
            TokenKind::LParen => ParseRule::new(Precedence::Call, Some(Parser::parse_grouping), Some(Parser::parse_call)),
            TokenKind::RParen => ParseRule::new(Precedence::None, None, None),
            TokenKind::LBracket => ParseRule::new(Precedence::Index, None, Some(Parser::parse_index)),
            TokenKind::RBracket => ParseRule::new(Precedence::None, None, None),
            TokenKind::Tilde => ParseRule::new(Precedence::None, Some(Parser::parse_unary), None),
            TokenKind::Bang => ParseRule::new(Precedence::None, Some(Parser::parse_unary), None),
            TokenKind::Global => ParseRule::new(Precedence::None, None, None),
            TokenKind::For => ParseRule::new(Precedence::None, None, None),
            TokenKind::TBool => ParseRule::new(Precedence::None, Some(Parser::parse_null_ptr), None),
            TokenKind::Length => ParseRule::new(Precedence::None, Some(Parser::parse_length_exp), None),
            TokenKind::True => ParseRule::new(Precedence::None, Some(Parser::parse_bool_lit), None),
            TokenKind::False => ParseRule::new(Precedence::None, Some(Parser::parse_bool_lit), None),
            TokenKind::Dot => ParseRule::new(Precedence::Proj, None, Some(Parser::parse_proj)),
            TokenKind::New => ParseRule::new(Precedence::None, Some(Parser::parse_new_exp), None),
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

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.next_token)
    }

    fn peek_n(&self, n: usize) -> Option<&Token> {
        self.tokens.get(self.next_token + n - 1)
    }

    fn consume(&mut self) -> Option<&Token> {
        let t = self.tokens.get(self.next_token);
        if t.is_some() {
            self.next_token += 1;
        }
        t
    }

    fn test_next_is(&mut self, kind: TokenKind) -> bool {
        self.peek().is_some_and(|t| t.kind == kind)
    }

    fn assert_next_is(&mut self, kind: TokenKind) -> ParseResult<&Token> {
        let Some(t) = self.consume() else { panic!("expected {kind:?} but got eof") };
        if t.kind == kind {
            Ok(t)
        } else {
            panic!("expected {kind:?} but found {:?}", t.kind);
        }
    }

    fn parse_separated<T>(&mut self, mut parse_fn: impl FnMut(&mut Self) -> ParseResult<T>, sep: TokenKind, end: TokenKind) -> ParseResult<(Vec<T>, &Token)> {
        let mut v = vec![];

        while !self.test_next_is(end) {
            let t = parse_fn(self)?;
            v.push(t);
            if !self.test_next_is(sep) {
                break;
            }
            self.consume();
        }

        let end_token = self.assert_next_is(end)?;
        Ok((v, end_token))
    }


    pub fn parse_program(&mut self) -> ParseResult<ast::Prog> {
        let mut decls = vec![];
        while let Some(t) = self.peek() {
            let decl = match t.kind {
                TokenKind::Global => {
                    let start = self.consume().unwrap().loc;
                    let TokenData::String(name) = self.assert_next_is(TokenKind::Ident)?.data.clone() else { unreachable!() };
                    self.assert_next_is(TokenKind::Eq)?;
                    let init = self.parse_exp()?; // todo: validate for gexp
                    let end = self.assert_next_is(TokenKind::Semi)?.loc;
                    let gdecl = ast::Gdecl {
                        name,
                        init,
                    };
                    let loc = Range::merge(start, end);
                    ast::Decl::Var(Node { loc, t: gdecl })
                },
                TokenKind::Struct => {
                    let start = self.consume().unwrap().loc;
                    let TokenData::String(name) = self.assert_next_is(TokenKind::UIdent)?.data.clone() else { unreachable!() };
                    self.assert_next_is(TokenKind::LBrace)?;
                    let (fields, end) = self.parse_separated(Parser::parse_field_decl, TokenKind::Semi, TokenKind::RBrace)?;
                    let tdecl = ast::Tdecl {
                        name,
                        fields,
                    };
                    let loc = Range::merge(start, end.loc);
                    ast::Decl::Type(Node { loc, t: tdecl })
                },
                _ => {
                    let start = t.loc;
                    let ret_ty = self.parse_ret_type()?;
                    let TokenData::String(name) = self.assert_next_is(TokenKind::Ident)?.data.clone() else { unreachable!() };
                    self.assert_next_is(TokenKind::LParen)?;
                    let (args, _) = self.parse_separated(Parser::parse_type_and_ident, TokenKind::Comma, TokenKind::RParen)?;
                    let (body, end) = self.parse_block()?;
                    let fdecl = ast::Fdecl {
                        ret_ty,
                        name,
                        args,
                        body,
                    };
                    let loc = Range::merge(start, end);
                    ast::Decl::Fun(Node { loc, t: fdecl })
                }
            };

            decls.push(decl);
        }
        Ok(decls)
    }

    fn parse_field_decl(&mut self) -> ParseResult<ast::Field> {
        let (ty, name) = self.parse_type_and_ident()?;
        Ok(ast::Field {
            ty,
            name,
        })
    }

    fn parse_type_and_ident(&mut self) -> ParseResult<(ast::Ty, ast::Ident)> {
        let ty = self.parse_type()?;
        let TokenData::String(ident) = self.assert_next_is(TokenKind::Ident)?.data.clone() else { unreachable!() };
        Ok((ty, ident))
    }

    pub fn parse_stmt(&mut self) -> ParseResult<Node<ast::Stmt>> {
        match self.peek().map(|t| t.kind) {
            Some(TokenKind::Var) => {
                let Node { loc, t: vdecl } = self.parse_vdecl()?;
                Ok(Node { loc, t: ast::Stmt::Decl(vdecl) })
            }
            Some(TokenKind::If | TokenKind::Ifq) => {
                self.parse_ifs()
            }
            Some(TokenKind::Return) => {
                let start = self.consume().unwrap().loc;
                if self.test_next_is(TokenKind::Semi) {
                    let end = self.consume().unwrap().loc;
                    let loc = Range::merge(start, end);
                    return Ok(Node { loc, t: ast::Stmt::Ret(None) });
                }

                let e = self.parse_exp()?;
                let end = self.assert_next_is(TokenKind::Semi)?.loc;
                let loc = Range::merge(start, end);
                Ok(Node { loc, t: ast::Stmt::Ret(Some(e)) })
            }
            Some(TokenKind::While) => {
                let start = self.consume().unwrap().loc;
                self.assert_next_is(TokenKind::LParen)?;
                let cond = self.parse_exp()?;
                self.assert_next_is(TokenKind::RParen)?;
                let (block, end) = self.parse_block()?;
                let loc = Range::merge(start, end);
                Ok(Node { loc, t: ast::Stmt::While(cond, block) })
            }
            Some(TokenKind::For) => {
                let start = self.consume().unwrap().loc;
                self.assert_next_is(TokenKind::LParen)?;
                let (decls, _semi) = self.parse_separated(|parser| parser.parse_vdecl().map(|node| node.t), TokenKind::Comma, TokenKind::Semi)?;

                let cond = if !self.test_next_is(TokenKind::Semi) {
                    Some(self.parse_exp()?)
                } else {
                    None
                };
                self.assert_next_is(TokenKind::Semi)?;

                let update = if !self.test_next_is(TokenKind::RParen) {
                    Some(Box::new(self.parse_stmt()?))
                } else {
                    None
                };
                self.assert_next_is(TokenKind::RParen)?;

                let (block, end) = self.parse_block()?;
                let loc = Range::merge(start, end);
                Ok(Node { loc, t: ast::Stmt::For(decls, cond, update, block) })
            }
            None => panic!("No input :/"),
            _ => {
                let e = self.parse_exp()?;
                let start = e.loc;
                match e.t {
                    ast::Exp::Call(name, args) => {
                        let end = self.assert_next_is(TokenKind::Semi)?.loc;
                        let loc = Range::merge(start, end);
                        Ok(Node { loc, t: ast::Stmt::Call(*name, args) })

                    }
                    lhs@(ast::Exp::Id(..) | ast::Exp::Proj(..) | ast::Exp::Index(..)) => {
                        let lhs = Node { loc: start, t: lhs };
                        self.assert_next_is(TokenKind::Eq)?;
                        let rhs = self.parse_exp()?;
                        let end = self.assert_next_is(TokenKind::Semi)?.loc;
                        let loc = Range::merge(start, end);
                        Ok(Node { loc, t: ast::Stmt::Assn(lhs, rhs) })
                    }
                    e => panic!("strange exp: {e:?}"),
                }
            }
        }
    }

    fn parse_else(&mut self, end: Range) -> ParseResult<(ast::Block, Range)> {
        if !self.test_next_is(TokenKind::Else) {
            return Ok((vec![], end));
        }

        self.consume();
        match self.peek().map(|t| t.kind) {
            Some(TokenKind::LBrace) => {
                self.parse_block()
            }
            Some(TokenKind::If | TokenKind::Ifq) => {
                let trailing_ifs = self.parse_ifs()?;
                let loc = trailing_ifs.loc;
                Ok((vec![trailing_ifs], loc))
            }
            _ => panic!("expected block or if statement after else"),
        }
    }

    fn parse_ifs(&mut self) -> ParseResult<Node<ast::Stmt>> {
        let iph = self.consume().unwrap();
        let start = iph.loc;
        match iph.kind {
            TokenKind::If => {
                self.assert_next_is(TokenKind::LParen)?;
                let cond = self.parse_exp()?;
                self.assert_next_is(TokenKind::RParen)?;
                let (if_block, end) = self.parse_block()?;
                let (else_block, end) = self.parse_else(end)?;
                let loc = Range::merge(start, end);
                Ok(Node { loc, t: ast::Stmt::If(cond, if_block, else_block) })
            }
            TokenKind::Ifq => {
                self.assert_next_is(TokenKind::LParen)?;
                let ref_ty = self.parse_ref_type()?;
                let TokenData::String(id) = self.assert_next_is(TokenKind::Ident)?.data.clone() else { unreachable!() };
                self.assert_next_is(TokenKind::Eq)?;
                let exp = self.parse_exp()?;
                self.assert_next_is(TokenKind::RParen)?;
                let (if_block, end) = self.parse_block()?;
                let (else_block, end) = self.parse_else(end)?;
                let loc = Range::merge(start, end);
                Ok(Node { loc, t: ast::Stmt::IfNull(ref_ty, id, exp, if_block, else_block) })
            }
            _ => unreachable!(),
        }
    }

    fn parse_block(&mut self) -> ParseResult<(ast::Block, Range)> {
        self.assert_next_is(TokenKind::LBrace)?;
        let (stmts, end) = self.parse_separated(Parser::parse_stmt, TokenKind::Semi, TokenKind::RBrace)?;
        Ok((stmts, end.loc))
    }

    fn parse_vdecl(&mut self) -> ParseResult<Node<ast::Vdecl>> {
        let start = self.consume().unwrap().loc;
        let TokenData::String(name) = self.assert_next_is(TokenKind::Ident)?.data.clone() else { unreachable!() };
        self.assert_next_is(TokenKind::Eq)?;
        let exp = self.parse_exp()?;
        let loc = Range::merge(start, exp.loc);
        Ok(Node { loc, t: ast::Vdecl { name, exp } })
    }

    pub fn parse_exp(&mut self) -> ParseResult<Node<ast::Exp>> {
        self.parse_precedence(Precedence::IOr)
    }

    fn parse_precedence(&mut self, precedence: Precedence) -> ParseResult<Node<ast::Exp>> {
        let rule = self.peek().and_then(|t| get_rule(t.kind).prefix);
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

            let infix = next_rule.and_then(|r| r.infix);
            if let Some(infix) = infix {
                lhs = infix(self, lhs)?;
            } else {
                // unreachable?
                panic!("expected infix rule fr!")
            }
        }

        Ok(lhs)
    }

    fn parse_field_exp(&mut self) -> ParseResult<(ast::Ident, Node<ast::Exp>)> {
        let name = self.assert_next_is(TokenKind::Ident)?;
        let TokenData::String(name) = name.data.clone() else { unreachable!() };
        self.assert_next_is(TokenKind::Eq)?;
        let exp = self.parse_exp()?;
        Ok((name, exp))
    }

    fn parse_array_helper(&mut self, starting_loc: Range, ty: ast::Ty) -> ParseResult<Node<ast::Exp>> {
        // new int[3]
        let len = self.parse_exp()?;
        let rbracket_loc = self.assert_next_is(TokenKind::RBracket)?.loc;
        if !self.test_next_is(TokenKind::LBrace) {
            let loc = Range::merge(starting_loc, rbracket_loc);
            return Ok(Node { loc, t: ast::Exp::ArrLen(ty, Box::new(len)) });
        }

        // new int[3]{ i -> i * i }
        self.consume();
        let ident = self.assert_next_is(TokenKind::Ident)?;
        let TokenData::String(name) = ident.data.clone() else { unreachable!() };
        self.assert_next_is(TokenKind::Arrow)?;
        let exp = self.parse_exp()?;
        let rbrace_loc = self.assert_next_is(TokenKind::RBrace)?.loc;
        let loc = Range::merge(starting_loc, rbrace_loc);
        Ok(Node { loc, t: ast::Exp::ArrInit(ty, Box::new(len), name, Box::new(exp)) })
    }

    fn parse_new_exp(&mut self) -> ParseResult<Node<ast::Exp>> {
        let new_loc = self.consume().unwrap().loc;
        let ty = self.parse_type()?; // todo: fumbles `new int[3]`
        let open = self.consume();
        match open.map(|o| o.kind) {
            Some(TokenKind::LBracket) => {
                self.parse_array_helper(new_loc, ty)
            }
            Some(TokenKind::LBrace) => {
                match ty.kind {
                    ast::TyKind::Struct(name) => {
                        if ty.nullable {
                            panic!("expected a struct name not a nullable struct type")
                        }
                        let (fields, rparen) = self.parse_separated(Parser::parse_field_exp, TokenKind::Semi, TokenKind::LBrace)?;
                        let loc = Range::merge(new_loc, rparen.loc);
                        Ok(Node { loc, t: ast::Exp::Struct(name, fields) })
                    }
                    ast::TyKind::Array(ty) => {
                        let (elems, rbrace) = self.parse_separated(Parser::parse_exp, TokenKind::Comma, TokenKind::RBrace)?;
                        let loc = Range::merge(new_loc, rbrace.loc);
                        Ok(Node { loc, t: ast::Exp::ArrElems(*ty, elems) })
                    }
                    _ => panic!("cannot use `new` to create non-struct or non-array types")
                }
            }
            // todo: these messages
            None => panic!("parsing failed in the middle of new expression"),
            _ => panic!("expected '{{' for a new struct or '[' for a new array")
        }
    }

    fn parse_length_exp(&mut self) -> ParseResult<Node<ast::Exp>> {
        let length_loc = self.consume().unwrap().loc;
        self.assert_next_is(TokenKind::LParen)?;
        let e = self.parse_exp()?;
        let rparen = self.assert_next_is(TokenKind::LParen)?;
        let loc = Range::merge(length_loc, rparen.loc);
        Ok(Node { loc, t: ast::Exp::Length(Box::new(e)) })
    }

    fn parse_null_ptr(&mut self) -> ParseResult<Node<ast::Exp>> {
        let start_loc = self.peek().unwrap().loc;
        let ty = self.parse_type()?;
        let null = self.assert_next_is(TokenKind::Null)?;
        let loc = Range::merge(start_loc, null.loc);
        Ok(Node { loc, t: ast::Exp::Null(ty) })
    }

    fn parse_call(&mut self, lhs: Node<ast::Exp>) -> ParseResult<Node<ast::Exp>> {
        self.consume().unwrap();
        let (args, rparen) = self.parse_separated(Parser::parse_exp, TokenKind::Comma, TokenKind::RParen)?;
        let loc = Range::merge(lhs.loc, rparen.loc);
        Ok(Node { loc, t: ast::Exp::Call(Box::new(lhs), args) })
    }

    fn parse_index(&mut self, lhs: Node<ast::Exp>) -> ParseResult<Node<ast::Exp>> {
        self.consume().unwrap();
        let index = self.parse_exp()?;
        let rbracket = self.assert_next_is(TokenKind::RBracket)?;
        let loc = Range::merge(lhs.loc, rbracket.loc);
        Ok(Node { loc, t: ast::Exp::Index(Box::new(lhs), Box::new(index)) })
    }

    fn parse_proj(&mut self, lhs: Node<ast::Exp>) -> ParseResult<Node<ast::Exp>> {
        self.consume().unwrap();
        let field = self.assert_next_is(TokenKind::Ident)?;
        let TokenData::String(field_name) = &field.data else { unreachable!() };
        let loc = Range::merge(lhs.loc, field.loc);
        Ok(Node { loc, t: ast::Exp::Proj(Box::new(lhs), field_name.clone()) })
    }

    // todo: this may also be a null function type (e.g. ()->int null)
    fn parse_grouping(&mut self) -> ParseResult<Node<ast::Exp>> {
        let lparen_loc = self.consume().unwrap().loc;
        let e = self.parse_exp()?;
        let rparen_loc = self.assert_next_is(TokenKind::RParen)?.loc;
        let loc = Range::merge(lparen_loc, rparen_loc);
        Ok(Node { loc, t: e.t })
    }

    fn parse_ident(&mut self) -> ParseResult<Node<ast::Exp>> {
        let ident = self.consume().unwrap();
        let TokenData::String(s) = &ident.data else { unreachable!() };
        Ok(Node { loc: ident.loc, t: ast::Exp::Id(s.clone()) })
    }

    fn parse_string_lit(&mut self) -> ParseResult<Node<ast::Exp>> {
        let string_lit = self.consume().unwrap();
        let TokenData::String(s) = &string_lit.data else { unreachable!() };
        Ok(Node { loc: string_lit.loc, t: ast::Exp::Str(s.clone()) })
    }

    fn parse_bool_lit(&mut self) -> ParseResult<Node<ast::Exp>> {
        let bool_lit = self.consume().unwrap();
        let val = match bool_lit.kind {
            TokenKind::True => true,
            TokenKind::False => false,
            _ => unreachable!(),
        };
        Ok(Node { loc: bool_lit.loc, t: ast::Exp::Bool(val) })
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
        let mut t = match self.peek().map(|t| t.kind) {
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
                let (mut arg_types, _) = self.parse_separated(Self::parse_type, TokenKind::Comma, TokenKind::RParen)?;
                // todo: hack for parenthesized types, would still parse '(int,)' as 'int' even though it is
                // invalid as a both parenthesized type and function type
                if arg_types.len() == 1 && !self.test_next_is(TokenKind::Arrow) {
                    arg_types.pop().unwrap()
                } else {
                    self.assert_next_is(TokenKind::Arrow)?;
                    let ret_ty = self.parse_ret_type()?;
                    ast::Ty::non_nullable(ast::TyKind::Fun(arg_types, Box::new(ret_ty)))
                }
            }
            None => panic!("expected type but found nothing!"),
            k => unimplemented!("unexpected token kind: {k:?}"),
        };

        loop {
            match self.peek().map(|t| t.kind) {
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
                    if !self.peek_n(2).map(|t| t.kind == TokenKind::RBracket).unwrap_or(false) {
                        break;
                    }
                    self.consume();
                    self.assert_next_is(TokenKind::RBracket)?;
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
            panic!("`void` is not a valid type, it's only valid as a return type");
        }
        Ok(ty)
    }

    fn parse_ref_type(&mut self) -> ParseResult<ast::Ty> {
        let ty = self.parse_any_type()?;
        if !ty.kind.is_ref() {
            panic!("expected a reference type, these are strings, arrays, classes, and functions");
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
    use ast::*;

    fn nl<T>(t: T) -> Node<T> {
        Node::no_loc(t)
    }

    fn bx<T>(t: T) -> Box<T> {
        Box::new(t)
    }

    fn ty(kind: TyKind) -> Ty {
        Ty { nullable: false, kind }
    }

    fn nty(kind: TyKind) -> Ty {
        Ty { nullable: true, kind }
    }

    fn lex_toks(s: &str) -> Vec<Token> {
        crate::oat::lexer::Lexer::new(s).lex_all()
    }

    fn exp_test(s: &str, expected: Node<Exp>) -> Result<(), ParseError> {
        let tokens = lex_toks(s);
        let e = Parser::new(tokens).parse_exp()?;
        assert_eq!(e, expected);
        Ok(())
    }

    #[test]
    fn parse_consts_1() -> Result<(), ParseError> {
        exp_test("bool[] null", nl(Exp::Null(ty(TyKind::Array(bx(ty(TyKind::Bool)))))))
    }

    #[test]
    fn parse_consts_2() -> Result<(), ParseError> {
        exp_test("42", nl(Exp::Int(42)))
    }

    #[test]
    fn parse_consts_3() -> Result<(), ParseError> {
        exp_test("true", nl(Exp::Bool(true)))
    }

    #[test]
    fn parse_consts_4() -> Result<(), ParseError> {
        exp_test("false", nl(Exp::Bool(false)))
    }

    #[test]
    fn parse_consts_5() -> Result<(), ParseError> {
        exp_test("\"hello world\"", nl(Exp::Str("hello world".to_string())))
    }

    #[test]
    fn parse_consts_6() -> Result<(), ParseError> {
        exp_test("new int[]{1, 2, 3}", nl(Exp::ArrElems(ty(TyKind::Int), vec![nl(Exp::Int(1)), nl(Exp::Int(2)), nl(Exp::Int(3))])))
    }
}
