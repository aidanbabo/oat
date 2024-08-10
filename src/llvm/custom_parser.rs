// todo: panic proof! no more indexing and always use .get!
// this will probably need a helper
// also do we need the lookahead? could it just be an interator and not a vec?

use std::collections::HashMap;

use internment::{Arena, ArenaIntern};

use super::lexer::{lex, Token, TokenKind, TokenData};
use super::ast::*;

#[derive(Debug)]
pub struct ParseError;

#[derive(Clone, Copy)]
struct Ctx<'a, 'b> {
    tokens: &'b [Token<'a>],
    index: usize,
    arena: &'a Arena<str>,
    uuid_next: usize,
}

impl<'a, 'b> Ctx<'a, 'b> {
    fn token_offset(&self, offset: usize) -> Option<&'b Token<'a>> {
        self.tokens.get(self.index + offset)
    }

    #[must_use]
    fn advanced(self, n: usize) -> Self {
        Ctx {
            index: self.index + n,
            ..self
        }
    }

    // remove mutable api ?
    fn gensym(&mut self, s: &str) -> ArenaIntern<'a, str> {
        let sym = self.arena.intern_string(format!("_{s}__{}", self.uuid_next));
        self.uuid_next += 1;
        sym
    }
}

type ParseResult<'a, 'b, T> = Result<(Ctx<'a, 'b>, T), ParseError>;

pub fn parse<'a>(input: &str, arena: &'a Arena<str>) -> Result<Prog<'a>, ParseError> {
    let tokens = lex(input, arena).unwrap();
    let mut ctx = Ctx {
        tokens: &tokens,
        index: 0,
        arena,
        uuid_next: 0,
    };

    let mut fdecls = Vec::new();
    let mut gdecls = Vec::new();
    let mut tdecls = HashMap::new();
    let mut edecls = Vec::new();
    while let Some(t) = ctx.token_offset(0) {
        match t.kind {
            TokenKind::Define => {
                let (c, fdecl) = fdecl(ctx)?;
                fdecls.push(fdecl);
                ctx = c;
            },
            TokenKind::Gid => {
                let (c, gdecl) = gdecl(ctx)?;
                gdecls.push(gdecl);
                ctx = c;
            }
            TokenKind::Uid => {
                let (c, (name, ty)) = tdecl(ctx)?;
                tdecls.insert(name, ty);
                ctx = c;
            },
            TokenKind::Declare => {
                let (c, edecl) = edecl(ctx)?;
                edecls.push(edecl);
                ctx = c;
            }
            _ => panic!("unexpected token"),
        }
    }

    Ok(Prog {
        tdecls,
        gdecls,
        fdecls,
        edecls,
    })

}

fn fdecl<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, (ArenaIntern<'a, str>, Fdecl<'a>)> {
    assert_eq!(ctx.token_offset(0).unwrap().kind, TokenKind::Define);
    let (ctx, ty) = tipe(ctx.advanced(1))?;

    let gid = ctx.token_offset(0).unwrap();
    let TokenData::Id(gid) = gid.data else { unreachable!() };
    assert_eq!(ctx.token_offset(1).unwrap().kind, TokenKind::LParen);
    let (ctx, args) = arglist(ctx.advanced(2))?;

    assert_eq!(ctx.token_offset(0).unwrap().kind, TokenKind::RParen);
    assert_eq!(ctx.token_offset(1).unwrap().kind, TokenKind::LBrace);
    let (ctx, eb) = entry_block(ctx.advanced(2))?;

    // todo: more blocks
    assert_eq!(ctx.tokens[ctx.index].kind, TokenKind::RBrace);

    let (ptys, pnames) = args.into_iter().unzip();
    let fd = Fdecl {
        ty: FunTy {
            params: ptys,
            ret: ty,
        },
        params: pnames,
        cfg: Cfg { entry: eb, blocks: Default::default() },
    };


    Ok((ctx.advanced(1), (gid, fd)))
}

fn arglist<'a, 'b>(mut ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Vec<(Ty<'a>, ArenaIntern<'a, str>)>> {
    let mut al = Vec::new();
    let mut first = true;
    loop {
        if !ctx.token_offset(0).is_some_and(|t| t.kind != TokenKind::RParen) {
            break;
        }

        if first {
            first = false;
        } else {
            assert_eq!(ctx.token_offset(0).unwrap().kind, TokenKind::Comma);
            ctx = ctx.advanced(1)
        };

        let ty;
        (ctx, ty) = tipe(ctx)?;

        let uid_tok = ctx.token_offset(0).unwrap();
        assert_eq!(uid_tok.kind, TokenKind::Uid);
        let TokenData::Id(uid) = uid_tok.data else { panic!() };
        al.push((ty, uid));
        ctx = ctx.advanced(1);
    }
    assert_eq!(ctx.token_offset(0).unwrap().kind, TokenKind::RParen);
    Ok((ctx, al))
}

fn entry_block<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Block<'a>> {
    if ctx.token_offset(0).unwrap().kind == TokenKind::Entry && ctx.token_offset(1).unwrap().kind == TokenKind::Colon {
        block(ctx.advanced(2))
    } else {
        block(ctx)
    }
}

fn block<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Block<'a>> {
    // todo: instructions
    let (mut ctx, term) = terminator(ctx)?;
    let sym = ctx.gensym("term");
    Ok((ctx, Block {
        insns: Vec::new(),
        term: (sym, term),
    }))
}

fn terminator<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Terminator<'a>> {
    match ctx.token_offset(0).unwrap().kind {
        TokenKind::Ret => {
            let (ctx, ty) = tipe(ctx.advanced(1))?;
            let (ctx, op) = if let Ok((new_ctx, op)) =  operand(ctx) {
                (new_ctx, Some(op))
            } else {
                (ctx, None)
            };
            Ok((ctx, Terminator::Ret(ty, op)))
        }
        _ => unimplemented!(),
    }
}

fn tipe<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Ty<'a>> {
    let t = ctx.token_offset(0).unwrap();
    let (mut ctx, mut ty) = match t.kind {
        TokenKind::Void => (ctx.advanced(1), Ty::Void),
        TokenKind::I1 => (ctx.advanced(1), Ty::I1),
        TokenKind::I8 => (ctx.advanced(1), Ty::I8),
        TokenKind::I32 => todo!(),
        TokenKind::I64 => (ctx.advanced(1), Ty::I64),
        TokenKind::LBrace => {
            todo!("struct types")
        },
        TokenKind::LBracket => {
            todo!("array types")
        }
        TokenKind::Uid => {
            let TokenData::Id(i) = t.data else { unreachable!() };
            (ctx.advanced(1), Ty::Named(i))
        }
        k => unimplemented!("{k:?}"),
    };

    // recursive case for for functions and pointers
    loop {
        let post = ctx.token_offset(0).unwrap();
        if post.kind == TokenKind::Star {
            ctx = ctx.advanced(1);
            ty = Ty::Ptr(Box::new(ty));
        } else {
            break;
        }
    }
    Ok((ctx, ty))
}

fn operand<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Operand<'a>> {
    let t = ctx.token_offset(0).unwrap();
    let op = match t.kind {
        TokenKind::Null => Operand::Null,
        TokenKind::IntLit => {
            let TokenData::Int(c) = t.data else { unreachable!() };
            Operand::Const(c)
        }
        TokenKind::Uid => {
            let TokenData::Id(i) = t.data else { unreachable!() };
            Operand::Id(i)
        }
        TokenKind::Gid => {
            let TokenData::Id(i) = t.data else { unreachable!() };
            Operand::Gid(i)
        }
        _ => panic!(),
    };
    Ok((ctx.advanced(1), op))
}

fn gdecl<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, (ArenaIntern<'a, str>, Gdecl<'a>)> {
    todo!()
}

fn tdecl<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, (ArenaIntern<'a, str>, Ty<'a>)> {
    todo!()
}

fn edecl<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, (ArenaIntern<'a, str>, Ty<'a>)> {
    todo!()
}
