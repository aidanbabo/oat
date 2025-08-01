use once_cell::sync::Lazy;

use std::collections::HashMap;

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
#[derive(Clone, Copy, Debug)]
enum TokenData {
    Int(i64),
    String(usize),
    End(usize),
    NoData,
}

#[derive(Clone, Copy, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub start: u32,
    data: TokenData,
}

impl Token {
    pub fn get_int(&self) -> i64 {
        let TokenData::Int(i) = self.data else { unreachable!("{self:?}") };
        i
    }

    // todo: uhhghghgh
    pub fn get_string(&self, input: &str) -> String {
        let TokenData::String(start) = self.data else { unreachable!("{self:?}") };
        // skip c at start of string lit
        string_literal(&mut input[start+1..].char_indices().peekable(), start).unwrap().1
    }

    pub fn get_id<'a>(&self, input: &'a str) -> &'a str {
        let TokenData::End(end) = self.data else { unreachable!("{self:?}") };
        &input[self.start as usize + 1 .. end]
    }

    pub fn get_end(&self) -> usize {
        let TokenData::End(ix) = self.data else { unreachable!("{self:?}") };
        ix
    }
}

#[derive(Debug, thiserror::Error)]
#[error("{0}")]
pub struct LexerError(pub(crate) String);

type CharIter<'a> = std::iter::Peekable<std::str::CharIndices<'a>>;

// todo: all interning in parser

pub fn lex(input: &str) -> Result<Vec<Token>, LexerError> {
    let mut char_iter: CharIter<'_> = input.char_indices().peekable();
    let mut tokens = Vec::new();

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
                    string_literal(&mut char_iter, ix)?.0
                } else {
                    keyword_or_label(&mut char_iter, input, ix)?
                }
            }
            '%' => ident(&mut char_iter, input, ix, false)?,
            '@' => ident(&mut char_iter, input, ix, true)?,
            '0'..='9' => digit(&mut char_iter, input, ix)?,
            c if c.is_ascii_alphabetic() || c == '_' => keyword_or_label(&mut char_iter, input, ix)?,
            _ => return Err(LexerError(format!("unexpected character {ch}"))),
        };
        tokens.push(token);
    }

    Ok(tokens)
}

fn no_data(kind: TokenKind, start: usize) -> Token {
    Token { kind, start: start as u32, data: TokenData::NoData }
}

fn keyword_or_label(iter: &mut CharIter<'_>, input: &str, start: usize) -> Result<Token, LexerError> {
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
            data: TokenData::End(end),
        })
    }
}

fn digit(iter: &mut CharIter<'_>, input: &str, start: usize) -> Result<Token, LexerError> {
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

fn ident(iter: &mut CharIter<'_>, input: &str, start: usize, global: bool) -> Result<Token, LexerError> {
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

    Ok(Token {
        kind: if global { TokenKind::Gid } else { TokenKind::Uid },
        start: start as u32,
        data: TokenData::End(end),
    })
}

// should we add support for all hex escapes?
// this means we may need to use Vec<u8> :(
fn string_literal(iter: &mut CharIter<'_>, start: usize) -> Result<(Token, String), LexerError> {
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

    Ok((
        Token {
            kind: TokenKind::StringLit,
            start: start as u32,
            data: TokenData::String(start),
        }, 
        out
    ))
}
