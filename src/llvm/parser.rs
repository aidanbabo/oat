// todo: panic proof! no more indexing and always use .get!
// this will probably need a helper
// also do we need the lookahead? could it just be an interator and not a vec?

use std::collections::HashMap;

use internment::{Arena, ArenaIntern};

use super::lexer::{lex, Token, TokenKind};
use super::ast::*;
use super::Interners;

#[derive(Clone, Debug, thiserror::Error)]
#[error("{0}")]
pub struct ParseError(String);

// todo as this type gets bigger maybe it's a bad idea to pass it around all the time
// function style :( or maybe we just box it :)
// or turn things inside it into references like interners and tokens
struct Ctx<'a, 'b> {
    tokens: Vec<Token>,
    index: usize,
    arena: &'a Arena<str>,
    uuid_next: usize,
    interners: Interners,
    input: &'b str,
}

impl<'a, 'b> Ctx<'a, 'b> {
    fn token_offset(&self, offset: usize) -> Option<Token> {
        self.tokens.get(self.index + offset).cloned()
    }

    #[must_use]
    fn advanced(self, n: usize) -> Self {
        Ctx {
            index: self.index + n,
            ..self
        }
    }

    fn gensym(self, s: &str) -> (Self, ArenaIntern<'a, str>) {
        let sym = self.arena.intern_string(format!("_{s}__{}", self.uuid_next));
        (Ctx {
            uuid_next: self.uuid_next + 1,
            ..self
        }, sym)
    }

    fn try_consume_token_of_kind(self, kind: TokenKind) -> Result<(Self, Token), (Self, Option<TokenKind>)> {
        if let Some(t) = self.token_offset(0) {
            if t.kind != kind {
                Err((self, Some(t.kind)))
            } else {
                Ok((self.advanced(1), t))
            }
        } else {
            Err((self, None))
        }
    }

    fn consume_token_of_kind(self, kind: TokenKind) -> Result<(Self, Token), ParseError> {
        self
            .try_consume_token_of_kind(kind)
            .map_err(|k| if let Some(k) = k.1 {
                ParseError(format!("Expected token of type {kind:?} but found token of kind {k:?}"))
            } else {
                ParseError(format!("Expected token of type {kind:?} but found nothing"))
            })
    }
}

type ParseResult<'a, 'b, T> = Result<(Ctx<'a, 'b>, T), ParseError>;

pub fn parse<'a, 'b>(input: &'b str, arena: &'a Arena<str>) -> Result<Prog<'a>, ParseError> {
    let tokens = lex(input).unwrap();
    let mut ctx = Ctx {
        tokens,
        index: 0,
        arena,
        uuid_next: 0,
        interners: Default::default(),
        input,
    };

    let mut fdecls: Vec<(Gid, Fdecl<'a>)> = Vec::new();
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
                let (mut c, gid) = ctx.consume_token_of_kind(TokenKind::Gid)?;
                let gid_id = c.interners.globals.intern(gid.get_id(c.input));
                let (c, _) = c.consume_token_of_kind(TokenKind::Equals)?;
                let (c, external) = if c.token_offset(0).map(|t| t.kind) == Some(TokenKind::External) {
                    (c.advanced(1), true)
                } else {
                    (c, false)
                };
                let (c, _) = c.consume_token_of_kind(TokenKind::Global)?;
                let (c, ty) = tipe(c)?;

                ctx = if external {
                    edecls.push((gid_id, ty));
                    c
                } else {
                    let (c, ginit) = ginit(c)?;
                    gdecls.push((gid_id, (ty, ginit)));
                    c
                };
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

    let Interners { labels, types, globals } = ctx.interners;
    Ok(Prog {
        tdecls,
        gdecls,
        fdecls,
        edecls,
        tables: LookupTables { 
            labels: labels.complete(),
            types: types.complete(),
            globals: globals.complete(),
        }
    })
}

fn fdecl<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, (Gid, Fdecl<'a>)> {
    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Define)?;
    let (ctx, ty) = tipe(ctx)?;

    let (ctx, gid) = ctx.consume_token_of_kind(TokenKind::Gid)?;
    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::LParen)?;
    // rparen included in arglist
    let (ctx, args) = arglist(ctx)?;
    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::LBrace)?;
    let (mut ctx, eb) = entry_block(ctx)?;

    let mut blocks = Vec::new();
    loop {
        let t = ctx.token_offset(0);
        if t.map(|t| t.kind) != Some(TokenKind::Lbl) {
            break;
        }

        let lbl;
        let blk;
        (ctx, lbl) = ctx.consume_token_of_kind(TokenKind::Lbl)?;
        (ctx, _) = ctx.consume_token_of_kind(TokenKind::Colon)?;
        (ctx, blk) = block(ctx)?;
        let lbl_end = lbl.get_end();
        let lbl_id = ctx.interners.labels.intern(&ctx.input[lbl.start as usize..lbl_end]);
        blocks.push((lbl_id, blk));
    }
    let (mut ctx, _) = ctx.consume_token_of_kind(TokenKind::RBrace)?;

    let (ptys, pnames) = args.into_iter().unzip();
    let fd = Fdecl {
        ty: FunTy {
            params: ptys,
            ret: ty,
        },
        params: pnames,
        cfg: Cfg { entry: eb, blocks },
    };


    let gid_id = ctx.interners.globals.intern(gid.get_id(ctx.input));
    Ok((ctx, (gid_id, fd)))
}

fn arglist<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Vec<(Ty, Uid<'a>)>> {
    token_separated(ctx, TokenKind::Comma, TokenKind::RParen, |ctx| {
        let (ctx, ty) = tipe(ctx)?;
        let (ctx, uid) = ctx.consume_token_of_kind(TokenKind::Uid)?;
        let uid_id = ctx.arena.intern(uid.get_id(ctx.input));
        Ok((ctx, (ty, uid_id)))
    })
}

fn entry_block<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Block<'a>> {
    if ctx.token_offset(0).unwrap().kind == TokenKind::Entry && ctx.token_offset(1).unwrap().kind == TokenKind::Colon {
        block(ctx.advanced(2))
    } else {
        block(ctx)
    }
}

fn block<'a, 'b>(mut ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Block<'a>> {
    let mut insns = Vec::new();
    ctx = loop {
        match maybe_instruction(ctx) {
            Ok(res) => {
                let uid;
                let insn;
                (ctx, (uid, insn)) = res?;
                insns.push((uid, insn));
            }
            Err(c) => break c,
        }
    };

    let (ctx, term) = terminator(ctx)?;
    let (ctx, sym) = ctx.gensym("term");
    Ok((ctx, Block {
        insns,
        term: (sym, term),
    }))
}

fn maybe_instruction<'a, 'b>(ctx: Ctx<'a, 'b>) -> Result<ParseResult<'a, 'b, (ArenaIntern<'a, str>, Insn<'a>)>, Ctx<'a, 'b>> {
    if matches!(ctx.token_offset(0).map(|t| t.kind), Some(TokenKind::Uid) | Some(TokenKind::Store) | Some(TokenKind::Call)) {
        Ok(instruction(ctx))
    } else {
        Err(ctx)
    }

}

fn instruction<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, (ArenaIntern<'a, str>, Insn<'a>)> {
    let Some(t0) = ctx.token_offset(0) else { 
        return Err(ParseError("expected a token to start instruction".to_string()));
    };

    match t0.kind {
        TokenKind::Uid => {
            let uid = ctx.arena.intern(t0.get_id(ctx.input));
            let (ctx, _) = ctx.advanced(1).consume_token_of_kind(TokenKind::Equals)?;
            // todo: silly looking
            let (uid, (ctx, insn)) = match ctx.token_offset(0).unwrap().kind {
                TokenKind::Or => (uid, binop(ctx.advanced(1), Bop::Or)?),
                TokenKind::Add => (uid, binop(ctx.advanced(1), Bop::Add)?),
                TokenKind::Sub => (uid, binop(ctx.advanced(1), Bop::Sub)?),
                TokenKind::Mul => (uid, binop(ctx.advanced(1), Bop::Mul)?),
                TokenKind::Shl => (uid, binop(ctx.advanced(1), Bop::Shl)?),
                TokenKind::Xor => (uid, binop(ctx.advanced(1), Bop::Xor)?),
                TokenKind::And => (uid, binop(ctx.advanced(1), Bop::And)?),
                TokenKind::Lshr => (uid, binop(ctx.advanced(1), Bop::Lshr)?),
                TokenKind::Ashr => (uid, binop(ctx.advanced(1), Bop::Ashr)?),
                TokenKind::Alloca => {
                    let (ctx, ty) = tipe(ctx.advanced(1))?;
                    (uid, (ctx, Insn::Alloca(ty)))
                }
                TokenKind::Load => {
                    let (ctx, ty) = tipe(ctx.advanced(1))?;
                    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Comma)?;
                    let (ctx, _ty) = tipe(ctx)?;
                    let (ctx, op) = operand(ctx)?;
                    (uid, (ctx, Insn::Load(ty, op)))
                }
                TokenKind::Icmp => {
                    let cnd = match ctx.token_offset(1).unwrap().kind {
                        TokenKind::Eq => Cnd::Eq,
                        TokenKind::Ne => Cnd::Ne,
                        TokenKind::Slt => Cnd::Slt,
                        TokenKind::Sle => Cnd::Sle,
                        TokenKind::Sgt => Cnd::Sgt,
                        TokenKind::Sge => Cnd::Sge,
                        k => return Err(ParseError(format!("invalid condition for icmp instruction {k:?}"))),
                    };
                    let (ctx, ty) = tipe(ctx.advanced(2))?;
                    let (ctx, o1) = operand(ctx)?;
                    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Comma)?;
                    let (ctx, o2) = operand(ctx)?;
                    (uid, (ctx, Insn::Icmp(cnd, ty, o1, o2)))
                }
                TokenKind::Bitcast => {
                    let (ctx, ty1) = tipe(ctx.advanced(1))?;
                    let (ctx, o) = operand(ctx)?;
                    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::To)?;
                    let (ctx, ty2) = tipe(ctx)?;
                    (uid, (ctx, Insn::Bitcast(ty1, o, ty2)))
                }
                TokenKind::Gep => {
                    let (ctx, ty) = tipe(ctx.advanced(1))?;
                    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Comma)?;
                    let (ctx, _ty) = tipe(ctx)?;
                    let (ctx, op) = operand(ctx)?;
                    let (mut ctx, _) = ctx.consume_token_of_kind(TokenKind::Comma)?;

                    let mut os = Vec::new();
                    let mut first = true;
                    ctx = loop {
                        let found_ty = ctx
                            .try_consume_token_of_kind(TokenKind::I32)
                            .or_else(|(ctx, _)| ctx.try_consume_token_of_kind(TokenKind::I64));
                        // either empty, or there was just a comma!
                        assert!(found_ty.is_ok() || first);

                        ctx = match found_ty {
                            Ok((c, _ty)) => {
                                let o;
                                (ctx, o) = operand(c)?;
                                os.push(o);
                                ctx
                            }
                            Err((c, _)) => {
                                break c;
                            }
                        };

                        if first {
                            first = false;
                        } 
                        ctx = match ctx.try_consume_token_of_kind(TokenKind::Comma) {
                            Ok((c, _)) => c,
                            Err((c, _)) => break c,
                        };
                    };

                    (uid, (ctx, Insn::Gep(ty, op, os)))
                }
                TokenKind::Call => (uid, call(ctx.advanced(1))?),
                k => return Err(ParseError(format!("unknown start to uid assigning instruction {k:?}"))),
            };
            Ok((ctx, (uid, insn)))
        }
        TokenKind::Store => {
            let (ctx, ty) = tipe(ctx.advanced(1))?;
            let (ctx, o1) = operand(ctx)?;
            let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Comma)?;
            let (ctx, _ty) = tipe(ctx)?;
            let (ctx, o2) = operand(ctx)?;
            let (ctx, sym) = ctx.gensym("store");
            Ok((ctx, (sym, Insn::Store(ty, o1, o2))))
        }
        TokenKind::Call => {
            let (ctx, sym) = ctx.gensym("call");
            let (ctx, ca) = call(ctx.advanced(1))?;
            Ok((ctx, (sym, ca)))
        }
        k => Err(ParseError(format!("unknown start to instruction {k:?}"))),
    }
}

fn call<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Insn<'a>> {
    let (ctx, ty) = tipe(ctx)?;
    let (ctx, op) = operand(ctx)?;
    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::LParen)?;
    let (ctx, args) = token_separated(ctx, TokenKind::Comma, TokenKind::RParen, |ctx| {
        let (ctx, ty) = tipe(ctx)?;
        let (ctx, op) = operand(ctx)?;
        Ok((ctx, (ty, op)))
    })?;
    Ok((ctx, Insn::Call(ty, op, args)))

}

fn binop<'a, 'b>(ctx: Ctx<'a, 'b>, bop: Bop) -> ParseResult<'a, 'b, Insn<'a>> {
    let (ctx, ty) = tipe(ctx)?;
    let (ctx, o1) = operand(ctx)?;
    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Comma)?;
    let (ctx, o2) = operand(ctx)?;
    Ok((ctx, Insn::Binop(bop, ty, o1, o2)))
}

fn terminator<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Terminator<'a>> {
    match ctx.token_offset(0).unwrap().kind {
        TokenKind::Ret => {
            let (ctx, ty) = tipe(ctx.advanced(1))?;
            let (ctx, op) = match try_operand(ctx) {
                Ok(res) => {
                    let (new_ctx, op) = res.unwrap();
                    (new_ctx, Some(op))
                }
                Err(ctx) => (ctx, None),
            };
            Ok((ctx, Terminator::Ret(ty, op)))
        }
        TokenKind::Br => {
            match ctx.token_offset(1).unwrap().kind {
                TokenKind::Label => {
                    let (mut ctx, lbl) = ctx.advanced(2).consume_token_of_kind(TokenKind::Uid)?;
                    let lbl_id = ctx.interners.labels.intern(lbl.get_id(ctx.input));
                    let term = Terminator::Br(lbl_id); 
                    Ok((ctx, term))
                }
                TokenKind::I1 => {
                    let (ctx, op) = operand(ctx.advanced(2))?;
                    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Comma)?;
                    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Label)?;
                    let (ctx, lbl1) = ctx.consume_token_of_kind(TokenKind::Uid)?;

                    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Comma)?;
                    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Label)?;
                    let (mut ctx, lbl2) = ctx.consume_token_of_kind(TokenKind::Uid)?;

                    let lbl1_id = ctx.interners.labels.intern(lbl1.get_id(ctx.input));
                    let lbl2_id = ctx.interners.labels.intern(lbl2.get_id(ctx.input));
                    let term = Terminator::Cbr(op, lbl1_id, lbl2_id);
                    Ok((ctx, term))
                }
                k => Err(ParseError(format!("invalid token after br: {k:?}"))),
            }
        }
        k => Err(ParseError(format!("unknown terminator start token: {k:?}")))
    }
}

fn tipe<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Ty> {
    let t = ctx.token_offset(0).unwrap();
    let mut ctx = ctx.advanced(1);
    let (mut ctx, mut ty) = match t.kind {
        TokenKind::Void => (ctx, Ty::Void),
        TokenKind::I1 => (ctx, Ty::I1),
        TokenKind::I8 => (ctx, Ty::I8),
        TokenKind::I32 => unreachable!("handled in gep implementation"),
        TokenKind::I64 => (ctx, Ty::I64),
        TokenKind::LBrace => {
            let (ctx, ts) = token_separated(ctx, TokenKind::Comma, TokenKind::RBrace, tipe)?;
            (ctx, Ty::Struct(ts))
        },
        TokenKind::LBracket => {
            let (ctx, len) = ctx.consume_token_of_kind(TokenKind::IntLit)?;
            let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Cross)?;
            let (ctx, nested_ty) = tipe(ctx)?;
            let (ctx, _) = ctx.consume_token_of_kind(TokenKind::RBracket)?;
            (ctx, Ty::Array(len.get_int(), Box::new(nested_ty)))
        }
        TokenKind::Uid => {
            let tid = ctx.interners.types.intern(t.get_id(ctx.input));
            (ctx, Ty::Named(tid))
        }
        k => return Err(ParseError(format!("unknown start token to type: {k:?}"))),
    };

    // recursive case for for functions and pointers
    loop {
        let post = ctx.token_offset(0).unwrap();
        if post.kind == TokenKind::Star {
            ctx = ctx.advanced(1);
            ty = Ty::Ptr(Box::new(ty));
        } else if post.kind == TokenKind::LParen {
            ctx = ctx.advanced(1);
            let ts;
            (ctx, ts) = token_separated(ctx, TokenKind::Comma, TokenKind::RParen, tipe)?;
            ty = Ty::Fun(ts, Box::new(ty));
        } else {
            break;
        }
    }
    Ok((ctx, ty))
}

fn operand<'a, 'b>(mut ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Operand<'a>> {
    let t = ctx.token_offset(0).unwrap();
    let op = match t.kind {
        TokenKind::Null => Operand::Null,
        TokenKind::IntLit => Operand::Const(t.get_int()),
        TokenKind::Uid => Operand::Id(ctx.arena.intern(t.get_id(ctx.input))),
        TokenKind::Gid => Operand::Gid(ctx.interners.globals.intern(t.get_id(ctx.input))),
        k => return Err(ParseError(format!("unknown start to operator {k:?}"))),
    };
    Ok((ctx.advanced(1), op))
}

// todo: kinda stupid, no reuse
// we luck out here since operands are only one token, this hack doesn't work generally
fn try_operand<'a, 'b>(mut ctx: Ctx<'a, 'b>) -> Result<ParseResult<'a, 'b, Operand<'a>>, Ctx<'a, 'b>> {
    let t = ctx.token_offset(0).unwrap();
    let op = match t.kind {
        TokenKind::Null => Operand::Null,
        TokenKind::IntLit => Operand::Const(t.get_int()),
        TokenKind::Uid => Operand::Id(ctx.arena.intern(t.get_id(ctx.input))),
        TokenKind::Gid => Operand::Gid(ctx.interners.globals.intern(t.get_id(ctx.input))),
        _ => return Err(ctx),
    };
    Ok(Ok((ctx.advanced(1), op)))
}

fn ginit<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, Ginit> {
    let t = ctx.token_offset(0).unwrap();
    let mut ctx = ctx.advanced(1);
    let init = match t.kind {
        TokenKind::Null => (ctx, Ginit::Null),
        TokenKind::Gid => {
            let gid = ctx.interners.globals.intern(t.get_id(ctx.input));
            (ctx, Ginit::Gid(gid))
        },
        TokenKind::IntLit => (ctx, Ginit::Int(t.get_int())),
        TokenKind::StringLit => {
            let s = t.get_string(ctx.input);
            (ctx, Ginit::String(s))
        }
        TokenKind::LBracket => {
            let (ctx, ginits) = gdecl_list(ctx, TokenKind::RBracket)?;
            (ctx, Ginit::Array(ginits))
        }
        TokenKind::LBrace => {
            let (ctx, ginits) = gdecl_list(ctx, TokenKind::RBrace)?;
            (ctx, Ginit::Struct(ginits))
        }
        TokenKind::Bitcast => {
            let (ctx, _) = ctx.consume_token_of_kind(TokenKind::LParen)?;
            let (ctx, t1) = tipe(ctx)?;
            let (ctx, g) = ginit(ctx)?;
            let (ctx, _) = ctx.consume_token_of_kind(TokenKind::To)?;
            let (ctx, t2) = tipe(ctx)?;
            let (ctx, _) = ctx.consume_token_of_kind(TokenKind::RParen)?;
            (ctx, Ginit::Bitcast(t1, Box::new(g), t2))
        }
        k => return Err(ParseError(format!("unexpected token to start global initializer {k:?}"))),
    };
    Ok(init)
}

fn gdecl_list<'a, 'b>(ctx: Ctx<'a, 'b>, end_token: TokenKind) -> ParseResult<'a, 'b, Vec<(Ty, Ginit)>> {
    token_separated(ctx, TokenKind::Comma, end_token, |ctx| {
        let (ctx, ty) = tipe(ctx)?;
        let (ctx, gi) = ginit(ctx)?;
        Ok((ctx, (ty, gi)))
    })
}

fn tdecl<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, (Tid, Ty)> {
    let (ctx, uid) = ctx.consume_token_of_kind(TokenKind::Uid)?;
    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Equals)?;
    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Type)?;
    let (mut ctx, ty) = tipe(ctx)?;
    let tid_ty = (ctx.interners.types.intern(uid.get_id(ctx.input)), ty);
    Ok((ctx, tid_ty))
}

fn edecl<'a, 'b>(ctx: Ctx<'a, 'b>) -> ParseResult<'a, 'b, (Gid, Ty)> {
    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::Declare)?;
    let (ctx, rty) = tipe(ctx)?;
    let (ctx, gid) = ctx.consume_token_of_kind(TokenKind::Gid)?;
    let (ctx, _) = ctx.consume_token_of_kind(TokenKind::LParen)?;
    let (mut ctx, ts) = token_separated(ctx, TokenKind::Comma, TokenKind::RParen, tipe)?;
    let gid_id = ctx.interners.globals.intern(gid.get_id(ctx.input));
    Ok((ctx, (gid_id, Ty::Fun(ts, Box::new(rty)))))
}

fn token_separated<'a, 'b, T, F>(mut ctx: Ctx<'a, 'b>, sep: TokenKind, end: TokenKind, mut fun: F) -> ParseResult<'a, 'b, Vec<T>>
where
    F: FnMut(Ctx<'a, 'b>) -> ParseResult<'a, 'b, T>
{
    let mut list = Vec::new();
    let mut first = true;
    loop {
        if !ctx.token_offset(0).is_some_and(|t| t.kind != end) {
            break;
        }

        if first {
            first = false;
        } else {
            (ctx, _) = ctx.consume_token_of_kind(sep)?;
        };

        let t;
        (ctx, t) = fun(ctx)?;
        list.push(t);
    }
    let (ctx, _) = ctx.consume_token_of_kind(end)?;
    Ok((ctx, list))
}
