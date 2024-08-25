use internment::{Arena, ArenaIntern};
use once_cell::sync::Lazy;

use std::collections::HashMap;

use crate::StrInterner;

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenKind {
    /// string literal
    StringLit,
    /// an integer literal
    IntLit,
    /// i1
    I1,
    /// i8
    I8,
    /// i32
    I32,
    /// i64
    I64,
    /// *
    Star,
    /// ,
    Comma,
    /// x
    Cross,
    /// :
    Colon,
    /// =
    Equals,
    /// (
    LParen,
    /// )
    RParen,
    /// {
    LBrace,
    /// }
    RBrace,
    /// [
    LBracket,
    /// ]
    RBracket,
    /// to
    To,
    /// br
    Br,
    /// eq
    Eq,
    /// ne
    Ne,
    /// or
    Or,
    /// and
    And,
    /// add
    Add,
    /// sub
    Sub,
    /// mul
    Mul,
    /// xor
    Xor,
    /// slt
    Slt,
    /// sle
    Sle,
    /// sgt
    Sgt,
    /// sge
    Sge,
    /// shl
    Shl,
    /// ret
    Ret,
    /// lshr
    Lshr,
    /// ashr
    Ashr,
    /// getelementptr
    Gep,
    /// type
    Type,
    /// null
    Null,
    /// call
    Call,
    /// icmp
    Icmp,
    /// void
    Void,
    /// load
    Load,
    /// store
    Store,
    /// entry
    Entry,
    /// label
    Label,
    /// global
    Global,
    /// define
    Define,
    /// declare
    Declare,
    /// external
    External,
    /// alloca
    Alloca,
    /// bitcast
    Bitcast,
    /// any uid, identifiers starting with a '%'
    Uid,
    /// any gid, identifiers starting with a '@'
    Gid,
    /// any label
    Lbl,
}

// todo: make this only an integer and use lookup tables for actual string names
// (this would remove lifetimes, arenaintern (probably) and save space)
// this would involve an ast level change, big boy breaking
#[derive(Clone, Debug)]
enum TokenData<'a> {
    Int(i64),
    String(Box<str>),
    Id(ArenaIntern<'a, str>),
    Ix(u32),
    NoData,
}

#[derive(Debug)]
pub struct Token<'a> {
    pub kind: TokenKind,
    pub start: u32,
    data: TokenData<'a>,
}

impl<'a> Token<'a> {
    pub fn get_int(&self) -> i64 {
        let TokenData::Int(i) = self.data else { unreachable!("{self:?}") };
        i
    }
    // todo: uhhghghgh
    pub fn get_str(&self) -> &str {
        let TokenData::String(ref s) = self.data else { unreachable!("{self:?}") };
        s
    }
    pub fn get_id(&self) -> ArenaIntern<'a, str> {
        let TokenData::Id(id) = self.data else { unreachable!("{self:?}") };
        id
    }
    pub fn get_ix(&self) -> u32 {
        let TokenData::Ix(id) = self.data else { unreachable!("{self:?}") };
        id
    }
    pub fn get_ix_from_id(&self, map: &HashMap<Box<str>, u32>) -> u32 {
        let TokenData::Id(id) = self.data else { unreachable!("{self:?}") };
        *map
            .get(&*id)
            .unwrap_or_else(|| panic!("existing mapping for id: {id}"))
    }
}

#[derive(Debug, thiserror::Error)]
#[error("{0}")]
pub struct LexerError(String);

type CharIter<'a> = std::iter::Peekable<std::str::CharIndices<'a>>;

pub fn lex<'a>(input: &str, arena: &'a Arena<str>) -> Result<(Vec<Token<'a>>, StrInterner), LexerError> {
    let mut char_iter: CharIter<'_> = input.char_indices().peekable();
    let mut tokens = Vec::new();
    let mut label_interner = StrInterner::default();

    while let Some((ix, ch)) = char_iter.next() {
        let token = match ch {
            '\t' | ' ' | '\r' | '\n' => continue,
            ';' => {
                for (_, c) in &mut char_iter {
                    if c == '\n' {
                        break;
                    }
                }
                continue;
            }
            '*' => no_data(TokenKind::Star, ix),
            ',' => no_data(TokenKind::Comma, ix),
            ':' => no_data(TokenKind::Colon, ix),
            '=' => no_data(TokenKind::Equals, ix),
            '(' => no_data(TokenKind::LParen, ix),
            ')' => no_data(TokenKind::RParen, ix),
            '{' => no_data(TokenKind::LBrace, ix),
            '}' => no_data(TokenKind::RBrace, ix),
            '[' => no_data(TokenKind::LBracket, ix),
            ']' => no_data(TokenKind::RBracket, ix),
            'c' => {
                if char_iter.peek().is_some_and(|(_, c)| *c == '"') {
                    string_literal(&mut char_iter, ix)?
                } else {
                    keyword_or_label(&mut char_iter, input, ix, &mut label_interner)?
                }
            }
            '%' => ident(&mut char_iter, input, ix, arena, false)?,
            '@' => ident(&mut char_iter, input, ix, arena, true)?,
            '0'..='9' => digit(&mut char_iter, input, ix)?,
            c if c.is_ascii_alphabetic() || c == '_' => keyword_or_label(&mut char_iter, input, ix, &mut label_interner)?,
            _ => return Err(LexerError(format!("unexpected character {ch}"))),
        };
        tokens.push(token);
    }

    Ok((tokens, label_interner))
}

fn no_data(kind: TokenKind, start: usize) -> Token<'static> {
    Token { kind, start: start as u32, data: TokenData::NoData }
}

fn keyword_or_label<'a>(iter: &mut CharIter<'_>, input: &str, start: usize, lbl_int: &mut StrInterner) -> Result<Token<'a>, LexerError> {
    static KEYWORDS: Lazy<HashMap<&'static str, TokenKind>> = Lazy::new(|| {
        let mut m = HashMap::new();
        m.insert("i1", TokenKind::I1);
        m.insert("i8", TokenKind::I8);
        m.insert("i32", TokenKind::I32);
        m.insert("i64", TokenKind::I64);
        m.insert("to", TokenKind::To);
        m.insert("br", TokenKind::Br);
        m.insert("eq", TokenKind::Eq);
        m.insert("ne", TokenKind::Ne);
        m.insert("or", TokenKind::Or);
        m.insert("xor", TokenKind::Xor);
        m.insert("and", TokenKind::And);
        m.insert("add", TokenKind::Add);
        m.insert("sub", TokenKind::Sub);
        m.insert("mul", TokenKind::Mul);
        m.insert("slt", TokenKind::Slt);
        m.insert("sle", TokenKind::Sle);
        m.insert("sgt", TokenKind::Sgt);
        m.insert("sge", TokenKind::Sge);
        m.insert("shl", TokenKind::Shl);
        m.insert("lshr", TokenKind::Lshr);
        m.insert("ashr", TokenKind::Ashr);
        m.insert("ret", TokenKind::Ret);
        m.insert("getelementptr", TokenKind::Gep);
        m.insert("type", TokenKind::Type);
        m.insert("null", TokenKind::Null);
        m.insert("call", TokenKind::Call);
        m.insert("icmp", TokenKind::Icmp);
        m.insert("void", TokenKind::Void);
        m.insert("load", TokenKind::Load);
        m.insert("entry", TokenKind::Entry);
        m.insert("store", TokenKind::Store);
        m.insert("label", TokenKind::Label);
        m.insert("global", TokenKind::Global);
        m.insert("define", TokenKind::Define);
        m.insert("declare", TokenKind::Declare);
        m.insert("external", TokenKind::External);
        m.insert("alloca", TokenKind::Alloca);
        m.insert("bitcast", TokenKind::Bitcast);
        m.insert("x", TokenKind::Cross);
        m
    });

    let end = loop {
        let Some((ix, ch)) = iter.peek().copied() else {
            break input.len();
        };
        if !ch.is_ascii_alphanumeric() && ch != '_' && ch != '.' {
            break ix;
        }
        iter.next();
    };

    let word = &input[start..end];
    if let Some(kind) = KEYWORDS.get(word) {
        Ok(no_data(*kind, start))
    } else {
        Ok(Token {
            kind: TokenKind::Lbl,
            start: start as u32,
            data: TokenData::Ix(lbl_int.intern(word)),
        })
    }
}

fn digit(iter: &mut CharIter<'_>, input: &str, start: usize) -> Result<Token<'static>, LexerError> {
    let end = loop {
        let Some((ix, ch)) = iter.peek().copied() else {
            break input.len();
        };
        if !ch.is_ascii_digit() {
            break ix;
        }
        iter.next();
    };

    let string = &input[start..end];
    let literal_value: i64 = string.parse().map_err(|_| LexerError(format!("unable to parse number {string}")))?;
    Ok(Token {
        kind: TokenKind::IntLit,
        start: start as u32,
        data: TokenData::Int(literal_value),
    })
}

fn ident<'a>(iter: &mut CharIter<'_>, input: &str, start: usize, arena: &'a Arena<str>, global: bool) -> Result<Token<'a>, LexerError> {
    if iter.peek().is_some_and(|(_, c)| *c == '.') {
        iter.next();
    }

    match iter.next() {
        Some((_, ch)) if ch.is_ascii_alphanumeric() || ch == '_' => {},
        _ => return Err(LexerError("Expected at least one ascii alphanumeric character or underscore to start identifier".to_string())),
    }

    let end = loop {
        let Some((ix, ch)) = iter.peek().copied() else {
            break input.len();
        };
        if !ch.is_ascii_alphanumeric() && ch != '.' && ch != '_' {
            break ix;
        }
        iter.next();
    };

    let total_string = &input[start..end];
    let ident = &total_string[1..];
    Ok(Token {
        kind: if global { TokenKind::Gid } else { TokenKind::Uid },
        start: start as u32,
        data: TokenData::Id(arena.intern(ident)),
    })
}

// should we add support for all hex escapes?
// this means we may need to use Vec<u8> :(
fn string_literal(iter: &mut CharIter<'_>, start: usize) -> Result<Token<'static>, LexerError> {
    assert!(matches!(iter.next(), Some((_, '"'))));

    let mut out = String::new();

    while let Some((_, c)) = iter.next() {
        if c == '\\' {
            let (_, c2) = iter.next().expect("escaped character");
            if c2 == '\\' {
                out.push('\\');
            } else if c2 == '"' {
                out.push('"');
            } else if c2 == '0' {
                iter.next().filter(|(_, c)| *c == '0').expect("second zero digit in hex escape");
                out.push('\0');
            }
        } else if c == '"' {
            break;
        } else {
            out.push(c);
        }
    }

    Ok(Token {
        kind: TokenKind::StringLit,
        start: start as u32,
        data: TokenData::String(out.into()),
    })
}
