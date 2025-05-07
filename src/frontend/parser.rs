use super::{ast, Range, Node};
use super::lexer::{Token, TokenKind, TokenData};

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("parse error: {0}")]
pub struct ParseError(String);

pub type ParseResult<T> = Result<T, ParseError>;

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    /// nothing!
    None,
    /// [|]
    IOr,
    /// [&]
    IAnd,
    /// |
    Or,
    /// &
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

fn precedence_of(tk: TokenKind) -> Precedence {
    use TokenKind as TK;
    match tk {
    TK::IOr => Precedence::IOr,
    TK::IAnd => Precedence::IAnd,
    TK::Bar => Precedence::Or,
    TK::Amper => Precedence::And,
    TK::EqEq | TK::BangEq => Precedence::Equality,
    TK::Gt | TK::Lt | TK::GtEq | TK::LtEq => Precedence::Comparison,
    TK::GtGt | TK::LtLt | TK::GtGtGt => Precedence::Bitshift,
    TK::Plus | TK::Dash => Precedence::Term,
    TK::Star => Precedence::Factor,
    TK::LBracket => Precedence::Index,
    TK::Dot => Precedence::Proj,
    TK::LParen => Precedence::Call,
    _ => Precedence::None,
    }
}

#[derive(Debug)]
pub struct Parser<'ast> {
    tokens: Vec<Token<'ast>>,
    next_token: usize,
}

impl<'ast> Parser<'ast> {
    pub fn new(tokens: Vec<Token<'ast>>) -> Self {
        Self {
            tokens,
            next_token: 0,
        }
    }

    fn peek(&self) -> Token<'ast> {
        self.peek_n(1)
    }

    fn peek_n(&self, n: usize) -> Token<'ast> {
        self.tokens.get(self.next_token + n - 1).copied().expect("stopped at eof token")
    }

    fn consume(&mut self) -> Token<'ast> {
        let t = self.tokens.get(self.next_token).copied().expect("stopped at eof token");
        if t.kind != TokenKind::Eof {
            self.next_token += 1;
        }
        t
    }

    fn test_next_is(&mut self, kind: TokenKind) -> bool {
        self.peek().kind == kind
    }

    fn assert_next_is(&mut self, kind: TokenKind) -> ParseResult<Token<'ast>> {
        let t = self.consume();
        if t.kind == kind {
            Ok(t)
        } else {
            Err(ParseError(format!("expected {kind:?} but found {:?}", t.kind)))
        }
    }

    fn parse_separated<T>(&mut self, mut parse_fn: impl FnMut(&mut Self) -> ParseResult<T>, sep: TokenKind, end: TokenKind) -> ParseResult<(Vec<T>, Token<'ast>)> {
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


    pub fn parse_program(&mut self) -> ParseResult<ast::Prog<'ast>> {
        let mut decls = vec![];
        loop {
            let t = self.peek();
            if t.kind == TokenKind::Eof {
                break;
            }

            let decl = match t.kind {
                TokenKind::Global => {
                    let start = self.consume().loc;
                    let TokenData::String(name) = self.assert_next_is(TokenKind::Ident)?.data else { unreachable!() };
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
                    let start = self.consume().loc;
                    let TokenData::String(name) = self.assert_next_is(TokenKind::UIdent)?.data else { unreachable!() };
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
                    let TokenData::String(name) = self.assert_next_is(TokenKind::Ident)?.data else { unreachable!() };
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

    fn parse_field_decl(&mut self) -> ParseResult<ast::Field<'ast>> {
        let (ty, name) = self.parse_type_and_ident()?;
        Ok(ast::Field {
            ty,
            name,
        })
    }

    fn parse_type_and_ident(&mut self) -> ParseResult<(ast::Ty<'ast>, ast::Ident<'ast>)> {
        let ty = self.parse_type()?;
        let TokenData::String(ident) = self.assert_next_is(TokenKind::Ident)?.data else { unreachable!() };
        Ok((ty, ident))
    }

    pub fn parse_stmt(&mut self) -> ParseResult<Node<ast::Stmt<'ast>>> {
        match self.peek().kind {
            TokenKind::Var => {
                let Node { loc, t: vdecl } = self.parse_vdecl()?;
                let end = self.assert_next_is(TokenKind::Semi)?.loc;
                let loc = Range::merge(loc, end);
                Ok(Node { loc, t: ast::Stmt::Decl(vdecl) })
            }
            TokenKind::If | TokenKind::Ifq => {
                self.parse_ifs()
            }
            TokenKind::Return => {
                let start = self.consume().loc;
                if self.test_next_is(TokenKind::Semi) {
                    let end = self.consume().loc;
                    let loc = Range::merge(start, end);
                    return Ok(Node { loc, t: ast::Stmt::Ret(None) });
                }

                let e = self.parse_exp()?;
                let end = self.assert_next_is(TokenKind::Semi)?.loc;
                let loc = Range::merge(start, end);
                Ok(Node { loc, t: ast::Stmt::Ret(Some(e)) })
            }
            TokenKind::While => {
                let start = self.consume().loc;
                self.assert_next_is(TokenKind::LParen)?;
                let cond = self.parse_exp()?;
                self.assert_next_is(TokenKind::RParen)?;
                let (block, end) = self.parse_block()?;
                let loc = Range::merge(start, end);
                Ok(Node { loc, t: ast::Stmt::While(cond, block) })
            }
            TokenKind::For => {
                let start = self.consume().loc;
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
                    e => Err(ParseError(format!("unexpected expression: {e:?}. expected void call or assignment"))),
                }
            }
        }
    }

    fn parse_else(&mut self, end: Range) -> ParseResult<(ast::Block<'ast>, Range)> {
        if !self.test_next_is(TokenKind::Else) {
            return Ok((vec![], end));
        }

        self.consume();
        match self.peek().kind {
            TokenKind::LBrace => {
                self.parse_block()
            }
            TokenKind::If | TokenKind::Ifq => {
                let trailing_ifs = self.parse_ifs()?;
                let loc = trailing_ifs.loc;
                Ok((vec![trailing_ifs], loc))
            }
            k => Err(ParseError(format!("expected block or if statement after else, found {k:?}"))),
        }
    }

    fn parse_ifs(&mut self) -> ParseResult<Node<ast::Stmt<'ast>>> {
        let iph = self.consume();
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
                let TokenData::String(id) = self.assert_next_is(TokenKind::Ident)?.data else { unreachable!() };
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

    fn parse_block(&mut self) -> ParseResult<(ast::Block<'ast>, Range)> {
        self.assert_next_is(TokenKind::LBrace)?;
        let mut stmts = vec![];
        while !self.test_next_is(TokenKind::RBrace) {
            let stmt = self.parse_stmt()?;
            stmts.push(stmt);
        }
        let end = self.assert_next_is(TokenKind::RBrace)?.loc;
        Ok((stmts, end))
    }

    fn parse_vdecl(&mut self) -> ParseResult<Node<ast::Vdecl<'ast>>> {
        let start = self.consume().loc;
        let TokenData::String(name) = self.assert_next_is(TokenKind::Ident)?.data else { unreachable!() };
        self.assert_next_is(TokenKind::Eq)?;
        let exp = self.parse_exp()?;
        let loc = Range::merge(start, exp.loc);
        Ok(Node { loc, t: ast::Vdecl { name, exp } })
    }

    pub fn parse_exp(&mut self) -> ParseResult<Node<ast::Exp<'ast>>> {
        self.parse_precedence(Precedence::IOr)
    }

    fn parse_precedence(&mut self, precedence: Precedence) -> ParseResult<Node<ast::Exp<'ast>>> {
        let token = self.peek();
        let mut lhs = match token.kind {
            TokenKind::IntLit => self.parse_int_lit()?,
            TokenKind::String => self.parse_string_lit()?,
            TokenKind::Ident => self.parse_ident()?,
            TokenKind::LParen => self.parse_grouping()?,
            TokenKind::Dash | TokenKind::Tilde | TokenKind::Bang => self.parse_unary()?,
            TokenKind::TBool | TokenKind::UIdent | TokenKind::TInt | TokenKind::TVoid | TokenKind::TString => self.parse_null_ptr()?,
            TokenKind::Length => self.parse_length_exp()?,
            TokenKind::True | TokenKind::False => self.parse_bool_lit()?,
            TokenKind::New => self.parse_new_exp()?,
            tk => return Err(ParseError(format!("illegal way to start expression {tk:?}"))),
        };

        loop {
            let next_precedence = precedence_of(self.peek().kind);
            if precedence > next_precedence {
                break;
            }
            let next_token = self.consume();
            lhs = match next_token.kind {
                TokenKind::LParen => self.parse_call(lhs, next_token)?,
                TokenKind::LBracket => self.parse_index(lhs, next_token)?,
                TokenKind::Dot => self.parse_proj(lhs, next_token)?,
                TokenKind::Plus | TokenKind::Dash | TokenKind::Star | TokenKind::EqEq | 
                TokenKind::Gt | TokenKind::GtEq | TokenKind::Lt | TokenKind::LtEq | TokenKind::BangEq | 
                TokenKind::Bar | TokenKind::Amper | TokenKind::IOr | TokenKind::IAnd | TokenKind::LtLt | 
                TokenKind::GtGt | TokenKind::GtGtGt => self.parse_binary(lhs, next_token)?,
                tk => return Err(ParseError(format!("{tk:?} is not an infix operator"))),
            };
        }

        Ok(lhs)
    }

    fn parse_field_exp(&mut self) -> ParseResult<(ast::Ident<'ast>, Node<ast::Exp<'ast>>)> {
        let name = self.assert_next_is(TokenKind::Ident)?;
        let TokenData::String(name) = name.data else { unreachable!() };
        self.assert_next_is(TokenKind::Eq)?;
        let exp = self.parse_exp()?;
        Ok((name, exp))
    }

    fn parse_array_helper(&mut self, starting_loc: Range, ty: ast::Ty<'ast>) -> ParseResult<Node<ast::Exp<'ast>>> {
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
        let TokenData::String(name) = ident.data else { unreachable!() };
        self.assert_next_is(TokenKind::Arrow)?;
        let exp = self.parse_exp()?;
        let rbrace_loc = self.assert_next_is(TokenKind::RBrace)?.loc;
        let loc = Range::merge(starting_loc, rbrace_loc);
        Ok(Node { loc, t: ast::Exp::ArrInit(ty, Box::new(len), name, Box::new(exp)) })
    }

    fn parse_new_exp(&mut self) -> ParseResult<Node<ast::Exp<'ast>>> {
        let new_loc = self.consume().loc;
        let ty = self.parse_type()?;
        match self.consume().kind {
            TokenKind::LBracket => {
                self.parse_array_helper(new_loc, ty)
            }
            TokenKind::LBrace => {
                match ty.kind {
                    ast::TyKind::Struct(name) => {
                        if ty.nullable {
                            return Err(ParseError("cannot new a nullable struct".to_string()));
                        }
                        let (fields, rparen) = self.parse_separated(Parser::parse_field_exp, TokenKind::Semi, TokenKind::RBrace)?;
                        let loc = Range::merge(new_loc, rparen.loc);
                        Ok(Node { loc, t: ast::Exp::Struct(name, fields) })
                    }
                    ast::TyKind::Array(ty) => {
                        let (elems, rbrace) = self.parse_separated(Parser::parse_exp, TokenKind::Comma, TokenKind::RBrace)?;
                        let loc = Range::merge(new_loc, rbrace.loc);
                        Ok(Node { loc, t: ast::Exp::ArrElems(*ty, elems) })
                    }
                    _ => Err(ParseError(format!("cannot use `new` to create non-struct or non-array types: {ty}"))),
                }
            }
            k => Err(ParseError(format!("expected '{{' for a new struct or '[' for a new array but found {k:?}"))),
        }
    }

    fn parse_length_exp(&mut self) -> ParseResult<Node<ast::Exp<'ast>>> {
        let length_loc = self.consume().loc;
        self.assert_next_is(TokenKind::LParen)?;
        let e = self.parse_exp()?;
        let rparen = self.assert_next_is(TokenKind::RParen)?;
        let loc = Range::merge(length_loc, rparen.loc);
        Ok(Node { loc, t: ast::Exp::Length(Box::new(e)) })
    }

    fn parse_null_ptr(&mut self) -> ParseResult<Node<ast::Exp<'ast>>> {
        let start_loc = self.peek().loc;
        let ty = self.parse_ref_type()?;
        let null = self.assert_next_is(TokenKind::Null)?;
        let loc = Range::merge(start_loc, null.loc);
        Ok(Node { loc, t: ast::Exp::Null(ty) })
    }

    fn parse_call(&mut self, lhs: Node<ast::Exp<'ast>>, _: Token) -> ParseResult<Node<ast::Exp<'ast>>> {
        let (args, rparen) = self.parse_separated(Parser::parse_exp, TokenKind::Comma, TokenKind::RParen)?;
        let loc = Range::merge(lhs.loc, rparen.loc);
        Ok(Node { loc, t: ast::Exp::Call(Box::new(lhs), args) })
    }

    fn parse_index(&mut self, lhs: Node<ast::Exp<'ast>>, _: Token) -> ParseResult<Node<ast::Exp<'ast>>> {
        let index = self.parse_exp()?;
        let rbracket = self.assert_next_is(TokenKind::RBracket)?;
        let loc = Range::merge(lhs.loc, rbracket.loc);
        Ok(Node { loc, t: ast::Exp::Index(Box::new(lhs), Box::new(index)) })
    }

    fn parse_proj(&mut self, lhs: Node<ast::Exp<'ast>>, _: Token) -> ParseResult<Node<ast::Exp<'ast>>> {
        let field = self.assert_next_is(TokenKind::Ident)?;
        let TokenData::String(field_name) = &field.data else { unreachable!() };
        let loc = Range::merge(lhs.loc, field.loc);
        Ok(Node { loc, t: ast::Exp::Proj(Box::new(lhs), *field_name) })
    }

    // todo: this may also be a null function type (e.g. ()->int null)
    fn parse_grouping(&mut self) -> ParseResult<Node<ast::Exp<'ast>>> {
        let lparen_loc = self.consume().loc;
        let e = self.parse_exp()?;
        let rparen_loc = self.assert_next_is(TokenKind::RParen)?.loc;
        let loc = Range::merge(lparen_loc, rparen_loc);
        Ok(Node { loc, t: e.t })
    }

    fn parse_ident(&mut self) -> ParseResult<Node<ast::Exp<'ast>>> {
        let ident = self.consume();
        let TokenData::String(s) = &ident.data else { unreachable!() };
        Ok(Node { loc: ident.loc, t: ast::Exp::Id(*s) })
    }

    fn parse_string_lit(&mut self) -> ParseResult<Node<ast::Exp<'ast>>> {
        let string_lit = self.consume();
        let TokenData::String(s) = &string_lit.data else { unreachable!() };
        Ok(Node { loc: string_lit.loc, t: ast::Exp::Str(*s) })
    }

    fn parse_bool_lit(&mut self) -> ParseResult<Node<ast::Exp<'ast>>> {
        let bool_lit = self.consume();
        let val = match bool_lit.kind {
            TokenKind::True => true,
            TokenKind::False => false,
            _ => unreachable!(),
        };
        Ok(Node { loc: bool_lit.loc, t: ast::Exp::Bool(val) })
    }

    fn parse_int_lit(&mut self) -> ParseResult<Node<ast::Exp<'ast>>> {
        let int_lit = self.consume();
        let TokenData::Int(val) = int_lit.data else { unreachable!() };
        Ok(Node { loc: int_lit.loc, t: ast::Exp::Int(val) })
    }

    fn parse_unary(&mut self) -> ParseResult<Node<ast::Exp<'ast>>> {
        let unop_token = self.consume();

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

    fn parse_binary(&mut self, lhs: Node<ast::Exp<'ast>>, binop: Token) -> ParseResult<Node<ast::Exp<'ast>>> {
        let binop_kind = binop.kind;
        let rhs_prec = precedence_of(binop_kind);
        let rhs = self.parse_precedence(rhs_prec.next())?;
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

    fn parse_any_type(&mut self) -> ParseResult<ast::Ty<'ast>> {
        let mut t = match self.peek().kind {
            TokenKind::TVoid => {
                self.consume();
                ast::Ty::non_nullable(ast::TyKind::Void)
            }
            TokenKind::TBool => {
                self.consume();
                ast::Ty::non_nullable(ast::TyKind::Bool)
            }
            TokenKind::TInt => {
                self.consume();
                ast::Ty::non_nullable(ast::TyKind::Int)
            }
            TokenKind::TString => {
                self.consume();
                ast::Ty::non_nullable(ast::TyKind::String)
            }
            TokenKind::UIdent => {
                let t = self.consume();
                let TokenData::String(name) = &t.data else { unreachable!() };
                ast::Ty::non_nullable(ast::TyKind::Struct(*name))
            }
            TokenKind::LParen => {
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
            k => return Err(ParseError(format!("unexpected token kind: {k:?} in type"))),
        };

        loop {
            match self.peek().kind {
                TokenKind::Question => {
                    self.consume();
                    if !t.kind.is_ref() {
                        return Err(ParseError(format!("{:?} is not a reference type and therefore cannot be nullable", t.kind)));
                    }
                    if t.nullable {
                        return Err(ParseError("can't make a nullable type nullable as it is not a reference type".to_string()));
                    }
                    t.nullable = true;
                }
                TokenKind::LBracket => {
                    if self.peek_n(2).kind != TokenKind::RBracket {
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

    fn parse_type(&mut self) -> ParseResult<ast::Ty<'ast>> {
        let ty = self.parse_any_type()?;
        if ty.kind == ast::TyKind::Void {
            return Err(ParseError("`void` is not a valid type, it's only valid as a return type".to_string()));
        }
        Ok(ty)
    }

    fn parse_ref_type(&mut self) -> ParseResult<ast::Ty<'ast>> {
        let ty = self.parse_any_type()?;
        if !ty.kind.is_ref() {
            return Err(ParseError("expected a reference type, these are strings, arrays, classes, and functions".to_string()));
        }
        if ty.nullable {
            return Err(ParseError("expected a reference type, nullable types are not reference types".to_string()));
        }
        Ok(ty)
    }

    fn parse_ret_type(&mut self) -> ParseResult<ast::Ty<'ast>> {
        self.parse_any_type()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::*;
    use internment::Arena;
    use crate::frontend::lexer::Lexer;

    fn nl<T>(t: T) -> Node<T> {
        Node::no_loc(t)
    }

    fn bx<T>(t: T) -> Box<T> {
        Box::new(t)
    }

    fn bnl<T>(t: T) -> Box<Node<T>> {
        bx(nl(t))
    }

    fn ty(kind: TyKind<'_>) -> Ty<'_> {
        Ty { nullable: false, kind }
    }

    fn bty(kind: TyKind<'_>) -> Box<Ty<'_>> {
        bx(ty(kind))
    }

    fn vd<'ast>(a: &'ast Arena<str>, s: &str, exp: Exp<'ast>) -> Vdecl<'ast> {
        Vdecl {
            name: a.intern(s),
            exp: nl(exp),
        }
    }

    fn lex_toks<'out>(s: &str, a: &'out Arena<str>) -> Vec<Token<'out>> {
        Lexer::new(s, a).lex_all().unwrap()
    }

    fn exp_test<F>(s: &str, expected_fn: F) -> Result<(), ParseError>
    where
        for<'ast> F: FnOnce(&'ast Arena<str>) -> Node<Exp<'ast>>,
    {
        let arena = Arena::new();
        let tokens = lex_toks(s, &arena);
        let exp = Parser::new(tokens).parse_exp()?;
        assert_eq!(exp, expected_fn(&arena));
        Ok(())
    }

    fn stmt_test<F>(s: &str, expected_fn: F) -> Result<(), ParseError>
    where
        for<'ast> F: FnOnce(&'ast Arena<str>) -> Node<Stmt<'ast>>,
    {
        let arena = Arena::new();
        let tokens = lex_toks(s, &arena);
        let stmt = Parser::new(tokens).parse_stmt()?;
        assert_eq!(stmt, expected_fn(&arena));
        Ok(())
    }

    #[test]
    fn parse_const_1() -> Result<(), ParseError> {
        exp_test("bool[] null", |_| nl(Exp::Null(ty(TyKind::Array(bx(ty(TyKind::Bool)))))))
    }

    #[test]
    fn parse_const_2() -> Result<(), ParseError> {
        exp_test("42", |_| nl(Exp::Int(42)))
    }

    #[test]
    fn parse_const_3() -> Result<(), ParseError> {
        exp_test("true", |_| nl(Exp::Bool(true)))
    }

    #[test]
    fn parse_const_4() -> Result<(), ParseError> {
        exp_test("false", |_| nl(Exp::Bool(false)))
    }

    #[test]
    fn parse_const_5() -> Result<(), ParseError> {
        exp_test("\"hello world\"", |arena| nl(Exp::Str(arena.intern("hello world"))))
    }

    #[test]
    fn parse_const_6() -> Result<(), ParseError> {
        exp_test("new int[]{1, 2, 3}", |_| nl(Exp::ArrElems(ty(TyKind::Int), vec![nl(Exp::Int(1)), nl(Exp::Int(2)), nl(Exp::Int(3))])))
    }

    #[test]
    fn parse_exp_1() -> Result<(), ParseError> {
        exp_test("1", |_| nl(Exp::Int(1)))
    }

    #[test]
    fn parse_exp_2() -> Result<(), ParseError> {
        exp_test("1+2", |_| nl(Exp::Bop(Binop::Add, bnl(Exp::Int(1)), bnl(Exp::Int(2)))))
    }

    #[test]
    fn parse_exp_3() -> Result<(), ParseError> {
        exp_test("1+2+3", |_| nl(Exp::Bop(Binop::Add, bnl(Exp::Bop(Binop::Add, bnl(Exp::Int(1)), bnl(Exp::Int(2)))), bnl(Exp::Int(3)))))
    }

    #[test]
    fn parse_exp_4() -> Result<(), ParseError> {
        exp_test("1+2*3", |_| nl(Exp::Bop(Binop::Add, bnl(Exp::Int(1)), bnl(Exp::Bop(Binop::Mul, bnl(Exp::Int(2)), bnl(Exp::Int(3)))))))
    }

    #[test]
    fn parse_exp_5() -> Result<(), ParseError> {
        exp_test("1+(2+3)", |_| nl(Exp::Bop(Binop::Add, bnl(Exp::Int(1)), bnl(Exp::Bop(Binop::Add, bnl(Exp::Int(2)), bnl(Exp::Int(3)))))))
    }

    #[test]
    fn parse_exp_6() -> Result<(), ParseError> {
        exp_test("(1+2)*3", |_| nl(Exp::Bop(Binop::Mul, bnl(Exp::Bop(Binop::Add, bnl(Exp::Int(1)), bnl(Exp::Int(2)))), bnl(Exp::Int(3)))))
    }

    #[test]
    fn parse_exp_7() -> Result<(), ParseError> {
        exp_test("1+2*3+4", |_| nl(Exp::Bop(Binop::Add, bnl(Exp::Bop(Binop::Add, bnl(Exp::Int(1)), bnl(Exp::Bop(Binop::Mul, bnl(Exp::Int(2)), bnl(Exp::Int(3)))))), bnl(Exp::Int(4)))))
    }

    #[test]
    fn parse_exp_8() -> Result<(), ParseError> {
        exp_test("1-2 == 3+4", |_| nl(Exp::Bop(Binop::Eq, bnl(Exp::Bop(Binop::Sub, bnl(Exp::Int(1)), bnl(Exp::Int(2)))), bnl(Exp::Bop(Binop::Add, bnl(Exp::Int(3)), bnl(Exp::Int(4)))))))
    }

    #[test]
    fn parse_exp_9() -> Result<(), ParseError> {
        exp_test("(1+2)*(3+4)", |_| nl(Exp::Bop(Binop::Mul, bnl(Exp::Bop(Binop::Add, bnl(Exp::Int(1)), bnl(Exp::Int(2)))), bnl(Exp::Bop(Binop::Add, bnl(Exp::Int(3)), bnl(Exp::Int(4)))))))
    }

    #[test]
    fn parse_exp_10() -> Result<(), ParseError> {
        exp_test("true & true | false", |_| nl(Exp::Bop(Binop::Or, bnl(Exp::Bop(Binop::And, bnl(Exp::Bool(true)), bnl(Exp::Bool(true)))), bnl(Exp::Bool(false)))))
    }

    #[test]
    fn parse_exp_11() -> Result<(), ParseError> {
        exp_test("true & (true | false)", |_| nl(Exp::Bop(Binop::And, bnl(Exp::Bool(true)), bnl(Exp::Bop(Binop::Or, bnl(Exp::Bool(true)), bnl(Exp::Bool(false)))))))
    }

    #[test]
    fn parse_exp_12() -> Result<(), ParseError> {
        exp_test("!(~5 == ~6) & -5+10 < 0", |_| nl(Exp::Bop(Binop::And, bnl(Exp::Uop(Unop::LogNot, bnl(Exp::Bop(Binop::Eq, bnl(Exp::Uop(Unop::BitNot, bnl(Exp::Int(5)))), bnl(Exp::Uop(Unop::BitNot, bnl(Exp::Int(6)))))))), bnl(Exp::Bop(Binop::Lt, bnl(Exp::Bop(Binop::Add, bnl(Exp::Uop(Unop::Neg, bnl(Exp::Int(5)))), bnl(Exp::Int(10)))), bnl(Exp::Int(0)))))))
    }

    #[test]
    fn parse_exp_13() -> Result<(), ParseError> {
        exp_test("1+2 >> (3-4 >>> 7*8) << 9", |_| nl(Exp::Bop(Binop::Shl, bnl(Exp::Bop(Binop::Shr, bnl(Exp::Bop(Binop::Add, bnl(Exp::Int(1)), bnl(Exp::Int(2)))), bnl(Exp::Bop(Binop::Sar, bnl(Exp::Bop(Binop::Sub, bnl(Exp::Int(3)), bnl(Exp::Int(4)))), bnl(Exp::Bop(Binop::Mul, bnl(Exp::Int(7)), bnl(Exp::Int(8)))))))), bnl(Exp::Int(9)))))
    }

    #[test]
    fn parse_exp_14() -> Result<(), ParseError> {
        exp_test("~5 >> 7 - 10 < 9 * -6-4 | !false", |_| nl(Exp::Bop(Binop::Or, bnl(Exp::Bop(Binop::Lt, bnl(Exp::Bop(Binop::Shr, bnl(Exp::Uop(Unop::BitNot, bnl(Exp::Int(5)))), bnl(Exp::Bop(Binop::Sub, bnl(Exp::Int(7)), bnl(Exp::Int(10)))))), bnl(Exp::Bop(Binop::Sub, bnl(Exp::Bop(Binop::Mul, bnl(Exp::Int(9)), bnl(Exp::Uop(Unop::Neg, bnl(Exp::Int(6)))))), bnl(Exp::Int(4)))))), bnl(Exp::Uop(Unop::LogNot, bnl(Exp::Bool(false)))))))
    }

    #[test]
    fn parse_exp_15() -> Result<(), ParseError> {
        exp_test("false == 2 >= 3 | true !=  9 - 10 <= 4", |_| nl(Exp::Bop(Binop::Or, bnl(Exp::Bop(Binop::Eq, bnl(Exp::Bool(false)), bnl(Exp::Bop(Binop::Gte, bnl(Exp::Int(2)), bnl(Exp::Int(3)))))), bnl(Exp::Bop(Binop::Neq, bnl(Exp::Bool(true)), bnl(Exp::Bop(Binop::Lte, bnl(Exp::Bop(Binop::Sub, bnl(Exp::Int(9)), bnl(Exp::Int(10)))), bnl(Exp::Int(4)))))))))
    }

    #[test]
    fn parse_exp_16() -> Result<(), ParseError> {
        exp_test("1-2*3+4 < 5 | 6+7-2 > 1 | true & false", |_| nl(Exp::Bop(Binop::Or, bnl(Exp::Bop(Binop::Or, bnl(Exp::Bop(Binop::Lt, bnl(Exp::Bop(Binop::Add, bnl(Exp::Bop(Binop::Sub, bnl(Exp::Int(1)), bnl(Exp::Bop(Binop::Mul, bnl(Exp::Int(2)), bnl(Exp::Int(3)))))), bnl(Exp::Int(4)))), bnl(Exp::Int(5)))), bnl(Exp::Bop(Binop::Gt, bnl(Exp::Bop(Binop::Sub, bnl(Exp::Bop(Binop::Add, bnl(Exp::Int(6)), bnl(Exp::Int(7)))), bnl(Exp::Int(2)))), bnl(Exp::Int(1)))))), bnl(Exp::Bop(Binop::And, bnl(Exp::Bool(true)), bnl(Exp::Bool(false)))))))
    }

    #[test]
    fn parse_exp_17() -> Result<(), ParseError> {
        exp_test("true [&] false | false [|] true & true", |_| nl(Exp::Bop(Binop::IOr, bnl(Exp::Bop(Binop::IAnd, bnl(Exp::Bool(true)), bnl(Exp::Bop(Binop::Or, bnl(Exp::Bool(false)), bnl(Exp::Bool(false)))))), bnl(Exp::Bop(Binop::And, bnl(Exp::Bool(true)), bnl(Exp::Bool(true)))))))
    }

    #[test]
    fn parse_exp_18() -> Result<(), ParseError> {
        exp_test("true [|] false [&] true & true | false", |_| nl(Exp::Bop(Binop::IOr, bnl(Exp::Bool(true)), bnl(Exp::Bop(Binop::IAnd, bnl(Exp::Bool(false)), bnl(Exp::Bop(Binop::Or, bnl(Exp::Bop(Binop::And, bnl(Exp::Bool(true)), bnl(Exp::Bool(true)))), bnl(Exp::Bool(false)))))))))
    }

    #[test]
    fn parse_exp_19() -> Result<(), ParseError> {
        exp_test("new int[3]", |_| nl(Exp::ArrLen(ty(TyKind::Int), bnl(Exp::Int(3)))))
    }

    #[test]
    fn parse_exp_20() -> Result<(), ParseError> {
        exp_test("bar (x, \"cis341\")", |a| nl(Exp::Call(bnl(Exp::Id(a.intern("bar"))), vec![nl(Exp::Id(a.intern("x"))), nl(Exp::Str(a.intern("cis341")))])))
    }

    #[test]
    fn parse_exp_21() -> Result<(), ParseError> {
        fn inta_maker(a: i64, b: i64) -> Node<Exp<'static>> {
            nl(Exp::ArrElems(ty(TyKind::Int), vec![nl(Exp::Int(a)), nl(Exp::Int(b))]))
        }
        exp_test("new int[][]{new int[]{10,11},new int[]{20,21},new int[]{30,31}}", |_| nl(Exp::ArrElems(ty(TyKind::Array(bty(TyKind::Int))), vec![inta_maker(10, 11), inta_maker(20, 21), inta_maker(30, 31)])))
    }

    #[test]
    fn parse_exp_22() -> Result<(), ParseError> {
        exp_test("proc1 ()", |a| nl(Exp::Call(bnl(Exp::Id(a.intern("proc1"))), vec![])))
    }

    #[test]
    fn parse_exp_23() -> Result<(), ParseError> {
        exp_test("array[0]", |a| nl(Exp::Index(bnl(Exp::Id(a.intern("array"))), bnl(Exp::Int(0)))))
    }

    #[test]
    fn parse_exp_24() -> Result<(), ParseError> {
        exp_test("i + y[1][1]", |a| nl(Exp::Bop(Binop::Add, bnl(Exp::Id(a.intern("i"))), bnl(Exp::Index(bnl(Exp::Index(bnl(Exp::Id(a.intern("y"))), bnl(Exp::Int(1)))), bnl(Exp::Int(1)))))))
    }

    #[test]
    fn parse_exp_25() -> Result<(), ParseError> {
        exp_test("-!~x[0][0]", |a| nl(Exp::Uop(Unop::Neg, bnl(Exp::Uop(Unop::LogNot, bnl(Exp::Uop(Unop::BitNot, bnl(Exp::Index(bnl(Exp::Index(bnl(Exp::Id(a.intern("x"))), bnl(Exp::Int(0)))), bnl(Exp::Int(0)))))))))))
    }

    #[test]
    fn parse_exp_26() -> Result<(), ParseError> {
        exp_test("print_string (string_concat (str1, str2))", |a| nl(Exp::Call(bnl(Exp::Id(a.intern("print_string"))), vec![nl(Exp::Call(bnl(Exp::Id(a.intern("string_concat"))), vec![nl(Exp::Id(a.intern("str1"))), nl(Exp::Id(a.intern("str2")))]))])))
    }

    #[test]
    fn parse_stmt_1() -> Result<(), ParseError> {
        stmt_test("var n = 8;", |a| nl(Stmt::Decl(vd(a, "n", Exp::Int(8)))))
    }

    #[test]
    fn parse_stmt_2() -> Result<(), ParseError> {
        stmt_test("var x=a[0];", |a| nl(Stmt::Decl(vd(a, "x", Exp::Index(bnl(Exp::Id(a.intern("a"))), bnl(Exp::Int(0)))))))
    }

    #[test]
    fn parse_stmt_3() -> Result<(), ParseError> {
        stmt_test("return;", |_| nl(Stmt::Ret(None)))
    }

    #[test]
    fn parse_stmt_4() -> Result<(), ParseError> {
        stmt_test("return x+y;", |a| nl(Stmt::Ret(Some(nl(Exp::Bop(Binop::Add, bnl(Exp::Id(a.intern("x"))), bnl(Exp::Id(a.intern("y")))))))))
    }

    #[test]
    fn parse_stmt_5() -> Result<(), ParseError> {
        stmt_test("a[j>>1]=v;", |a| nl(Stmt::Assn(nl(Exp::Index(bnl(Exp::Id(a.intern("a"))), bnl(Exp::Bop(Binop::Shr, bnl(Exp::Id(a.intern("j"))), bnl(Exp::Int(1)))))), nl(Exp::Id(a.intern("v"))))))
    }

    #[test]
    fn parse_stmt_6() -> Result<(), ParseError> {
        stmt_test("foo(a,1,n);", |a| nl(Stmt::Call(nl(Exp::Id(a.intern("foo"))), vec![nl(Exp::Id(a.intern("a"))), nl(Exp::Int(1)), nl(Exp::Id(a.intern("n")))])))
    }

    #[test]
    fn parse_stmt_7() -> Result<(), ParseError> {
        stmt_test("a[i]=a[i>>1];", |a| nl(Stmt::Assn(nl(Exp::Index(bnl(Exp::Id(a.intern("a"))), bnl(Exp::Id(a.intern("i"))))), nl(Exp::Index(bnl(Exp::Id(a.intern("a"))), bnl(Exp::Bop(Binop::Shr, bnl(Exp::Id(a.intern("i"))), bnl(Exp::Int(1)))))))))
    }

    #[test]
    fn parse_stmt_8() -> Result<(), ParseError> {
        stmt_test("var a = new int[8];", |a| nl(Stmt::Decl(vd(a, "a", Exp::ArrLen(ty(TyKind::Int), bnl(Exp::Int(8)))))))
    }

    #[test]
    fn parse_stmt_9() -> Result<(), ParseError> {
        stmt_test("if((j<n)&(a[j]<a[j+1])) { j=j+1; }", |a| nl(Stmt::If(nl(Exp::Bop(Binop::And, bnl(Exp::Bop(Binop::Lt, bnl(Exp::Id(a.intern("j"))), bnl(Exp::Id(a.intern("n"))))), bnl(Exp::Bop(Binop::Lt, bnl(Exp::Index(bnl(Exp::Id(a.intern("a"))), bnl(Exp::Id(a.intern("j"))))), bnl(Exp::Index(bnl(Exp::Id(a.intern("a"))), bnl(Exp::Bop(Binop::Add, bnl(Exp::Id(a.intern("j"))), bnl(Exp::Int(1)))))))))), vec![nl(Stmt::Assn(nl(Exp::Id(a.intern("j"))), nl(Exp::Bop(Binop::Add, bnl(Exp::Id(a.intern("j"))), bnl(Exp::Int(1))))))], vec![])))
    }

    #[test]
    fn parse_stmt_10() -> Result<(), ParseError> {
        fn decl<'ast>(a: &'ast Arena<str>, s: &str) -> Node<Stmt<'ast>> {
            nl(Stmt::Decl(vd(a, s, Exp::Int(0))))
        }
        stmt_test("if(c == 1) { var i = 0; var j = 0; var k = 0; }", |a| nl(Stmt::If(nl(Exp::Bop(Binop::Eq, bnl(Exp::Id(a.intern("c"))), bnl(Exp::Int(1)))), vec![decl(a, "i"), decl(a, "j"), decl(a, "k")], vec![])))
    }

    #[test]
    fn parse_stmt_11() -> Result<(), ParseError> {
        fn ishift(a: &Arena<str>) -> Exp<'_> {
            Exp::Bop(Binop::Shr, bnl(Exp::Id(a.intern("i"))), bnl(Exp::Int(1)))
        }
        fn ashift(a: &Arena<str>) -> Exp<'_> {
            Exp::Index(bnl(Exp::Id(a.intern("a"))), bnl(ishift(a)))
        }
        stmt_test("while((i>1)&(a[i>>1]<v)) { a[i]=a[i>>1]; i=i>>1; }", |a| nl(Stmt::While(nl(Exp::Bop(Binop::And, bnl(Exp::Bop(Binop::Gt, bnl(Exp::Id(a.intern("i"))), bnl(Exp::Int(1)))), bnl(Exp::Bop(Binop::Lt, bnl(ashift(a)), bnl(Exp::Id(a.intern("v"))))))), vec![nl(Stmt::Assn(nl(Exp::Index(bnl(Exp::Id(a.intern("a"))), bnl(Exp::Id(a.intern("i"))))), nl(ashift(a)))), nl(Stmt::Assn(nl(Exp::Id(a.intern("i"))), nl(ishift(a))))])))
    }

    #[test]
    fn parse_stmt_12() -> Result<(), ParseError> {
        fn assn<'ast>(lhs: Exp<'ast>, rhs: Exp<'ast>) -> Node<Stmt<'ast>> {
            nl(Stmt::Assn(nl(lhs), nl(rhs)))
        }
        fn nums_i(a: &Arena<str>) -> Exp<'_> {
            Exp::Index(bnl(Exp::Id(a.intern("numbers"))), bnl(Exp::Id(a.intern("i"))))
        }
        fn nums_j(a: &Arena<str>) -> Exp<'_> {
            Exp::Index(bnl(Exp::Id(a.intern("numbers"))), bnl(Exp::Bop(Binop::Sub, bnl(Exp::Id(a.intern("j"))), bnl(Exp::Int(1)))))
        }
        fn temp(a: &Arena<str>) -> Exp<'_> {
            Exp::Id(a.intern("temp"))
        }

        fn inner_if(a: &Arena<str>) -> Node<Stmt<'_>> {
            nl(Stmt::If(nl(Exp::Bop(Binop::Gt, bnl(nums_j(a)), bnl(nums_i(a)))), vec![assn(temp(a), nums_j(a)), assn(nums_j(a), nums_i(a)), assn(nums_i(a), temp(a))], vec![]))
        }
        fn inner_for(a: &Arena<str>) -> Node<Stmt<'_>> {
            nl(Stmt::For(vec![vd(a, "j", Exp::Int(1))], Some(nl(Exp::Bop(Binop::Lte, bnl(Exp::Id(a.intern("j"))), bnl(Exp::Id(a.intern("i")))))), Some(bnl(Stmt::Assn(nl(Exp::Id(a.intern("j"))), nl(Exp::Bop(Binop::Add, bnl(Exp::Id(a.intern("j"))), bnl(Exp::Int(1))))))), vec![inner_if(a)]))
        }
        stmt_test("for (; i > 0; i=i-1;) { for (var j = 1; j <= i; j=j+1;) { if (numbers[j-1] > numbers[i]) { temp = numbers[j-1]; numbers[j-1] = numbers[i]; numbers[i] = temp; } } }", |a| nl(Stmt::For(vec![], Some(nl(Exp::Bop(Binop::Gt, bnl(Exp::Id(a.intern("i"))), bnl(Exp::Int(0))))), Some(bnl(Stmt::Assn(nl(Exp::Id(a.intern("i"))), nl(Exp::Bop(Binop::Sub, bnl(Exp::Id(a.intern("i"))), bnl(Exp::Int(1))))))), vec![inner_for(a)])))
    }

    #[test]
    fn parse_stmt_13() -> Result<(), ParseError> {
        stmt_test("for (var i = 0, var j = 0; ;) { }", |a| nl(Stmt::For(vec![vd(a, "i", Exp::Int(0)), vd(a, "j", Exp::Int(0))], None, None, vec![])))
    }
}
