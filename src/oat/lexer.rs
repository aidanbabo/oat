use once_cell::sync::Lazy;
use internment::{Arena, ArenaIntern};

use std::iter::Peekable;
use std::str::CharIndices;
use std::collections::HashMap;

use super::Range;

// bloom filter ? (oooooo aaaaaaa)
static KEYWORDS: Lazy<HashMap<&'static str, TokenKind>> = Lazy::new(|| {
    let mut m = HashMap::new();
    m.insert("struct", TokenKind::Struct);
    m.insert("null", TokenKind::Null);
    m.insert("void", TokenKind::TVoid);
    m.insert("int", TokenKind::TInt);
    m.insert("string", TokenKind::TString);
    m.insert("else", TokenKind::Else);
    m.insert("if", TokenKind::If);
    m.insert("while", TokenKind::While);
    m.insert("return", TokenKind::Return);
    m.insert("var", TokenKind::Var);
    m.insert("global", TokenKind::Global);
    m.insert("length", TokenKind::Length);
    m.insert("for", TokenKind::For);
    m.insert("new", TokenKind::New);
    m.insert("true", TokenKind::True);
    m.insert("false", TokenKind::False);
    m.insert("bool", TokenKind::TBool);
    m
});

#[derive(Clone, Debug, thiserror::Error)]
#[error("{message}")]
pub struct LexerError {
    location: Range,
    message: String,
}

#[derive(Clone, Copy, Debug)]
pub struct Token<'output> {
    pub loc: Range,
    pub kind: TokenKind,
    pub data: TokenData<'output>,
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum TokenKind {
    /// end of file
    Eof,
    /// [0-9]+ | 0x[0-9a-fA-F]+
    IntLit,
    /// null
    Null,
    /// a " delimited string
    String,
    /// an identifier
    Ident,
    /// an uppercase identifier (for types)
    UIdent,
    /// int
    TInt,
    /// void
    TVoid,
    /// string
    TString,
    /// if
    If,
    /// if?
    Ifq,
    /// else
    Else,
    /// while
    While,
    /// return
    Return,
    /// var
    Var,
    /// struct
    Struct,
    /// ;
    Semi,
    /// ,
    Comma,
    /// {
    LBrace,
    /// }
    RBrace,
    /// +
    Plus,
    /// -
    Dash,
    /// *
    Star,
    /// ==
    EqEq,
    /// =
    Eq,
    /// (
    LParen,
    /// )
    RParen,
    /// [
    LBracket,
    /// ]
    RBracket,
    /// ~
    Tilde,
    /// !
    Bang,
    /// global
    Global,
    /// for
    For,
    /// bool
    TBool,
    /// length
    Length,
    /// true
    True,
    /// false
    False,
    /// .
    Dot,
    /// new
    New,
    /// >
    Gt,
    /// >=
    GtEq,
    /// <
    Lt,
    /// <=
    LtEq,
    /// !=
    BangEq,
    /// |
    Bar,
    /// &
    Amper,
    /// [|]
    IOr,
    /// [&]
    IAnd,
    /// <<
    LtLt,
    /// >>
    GtGt,
    /// >>>
    GtGtGt,
    /// ->
    Arrow,
    /// ?
    Question,
}

#[derive(Clone, Copy, Debug)]
pub enum TokenData<'output> {
    Int(i64),
    String(ArenaIntern<'output, str>),
    None,
}

impl<'output> Token<'output> {
    fn one_line(kind: TokenKind, line: usize, start: usize, len: usize, data: TokenData<'output>) -> Self {
        Token {
            loc: Range { 
                start: (line, start),
                end: (line, start + len),
            },
            kind,
            data,
        }
    }
}

pub struct Lexer<'input, 'output> {
    input: &'input str,
    line: usize,
    line_start: usize,
    chars: Peekable<CharIndices<'input>>,
    arena: &'output Arena<str>,
}

impl<'input, 'output> Lexer<'input, 'output> {
    pub fn new(input: &'input str, arena: &'output Arena<str>) -> Self {
        Self {
            input,
            line: 1,
            line_start: 0,
            chars: input.char_indices().peekable(),
            arena,
        }
    }

    fn single(&mut self, kind: TokenKind) -> Token<'static> {
        let (i, _) = self.chars.next().unwrap();
        Token::one_line(kind, self.line, i - self.line_start, 1, TokenData::None)
    }

    fn maybe_double(&mut self, single_kind: TokenKind, second_char: char, double_kind: TokenKind) -> Token<'static> {
        let (i, _) = self.chars.next().unwrap();
        let (kind, len) = match self.chars.peek() {
            Some((_, c)) if second_char == *c => {
                self.chars.next().unwrap();
                (double_kind, 2)
            }
            _ => (single_kind, 1)
        };

        Token::one_line(kind, self.line, i - self.line_start, len, TokenData::None)
    }

    fn integer(&mut self) -> Result<Token<'static>, LexerError> {
        let (start, c0) = self.chars.next().unwrap();
        let mut end = start;
        let mut hex = false;
        let mut num = if c0 == '0' {
            if let Some((_, 'x')) = self.chars.peek() {
                end = self.chars.next().unwrap().0;
                hex = true;
            }
            Some(0i64)
        } else {
            Some(c0 as i64 - '0' as i64)
        };

        let multiplier = if hex { 16 } else { 10 };
        let mut c;
        loop {
            match self.chars.peek().map(|(_, c)| c) {
                Some('0'..='9') => {
                    (end, c) = self.chars.next().unwrap();
                    num = num.and_then(|n| n.checked_mul(multiplier)).and_then(|n| n.checked_add(c as i64 - '0' as i64));
                }
                Some('a'..='f') if hex => {
                    (end, c) = self.chars.next().unwrap();
                    num = num.and_then(|n| n.checked_mul(multiplier)).and_then(|n| n.checked_add(c as i64 - 'a' as i64 + 10 ));
                }
                Some('A'..='F') if hex => {
                    (end, c) = self.chars.next().unwrap();
                    num = num.and_then(|n| n.checked_mul(multiplier)).and_then(|n| n.checked_add(c as i64 - 'A' as i64 + 10 ));
                }
                _ => break,
            }
        }
        if let Some(n) = num {
            Ok(Token::one_line(TokenKind::IntLit, self.line, start - self.line_start, end + 1 - start, TokenData::Int(n)))
        } else {
            Err(LexerError { 
                location: Range { 
                    start: (self.line, start - self.line_start),
                    end: (self.line, start + end),
                },
                message: "integer literal is too large for an i64".to_string(),
            })
        }
    }

    fn any_ident(&mut self) -> (usize, usize) {
        let (start, _) = self.chars.next().unwrap();
        let mut end = start;
        while let Some('a'..='z' | 'A'..='Z' | '_' | '0'..='9') = self.chars.peek().map(|(_, c)| c) {
            end = self.chars.next().unwrap().0;
        }
        end += 1;
        (start, end)
    }

    fn uident(&mut self) -> Token<'output> {
        let (start, end) = self.any_ident();
        let s = &self.input[start..end];
        Token::one_line(TokenKind::UIdent, self.line, start - self.line_start, end - start, TokenData::String(self.arena.intern(s)))
    }

    fn ident(&mut self) -> Token<'output> {
        let (start, mut end) = self.any_ident();
        let s = &self.input[start..end];
        let (kind, data) = if let Some(kind) = KEYWORDS.get(s) {
            let k = match self.chars.peek().map(|(_, c)| c) {
                Some('?') if *kind == TokenKind::If => {
                    self.chars.next().unwrap();
                    end += 1;
                    TokenKind::Ifq
                }
                _ => *kind,
            };
            (k, TokenData::None)
        } else {
            (TokenKind::Ident, TokenData::String(self.arena.intern(s)))
        };
        Token::one_line(kind, self.line, start - self.line_start, end - start, data)
    }

    fn string(&mut self) -> Result<Token<'output>, LexerError> {
        let (start, _) = self.chars.next().unwrap();
        let start_line = self.line;
        let start_col = start - self.line_start;
        let mut contents = String::new();
        let end = loop {
            let error_maker = {
                let line = self.line;
                let line_start = self.line_start;
                move |end, message| LexerError {
                    location: Range { start: (start_line, start_col), end: (line, end - line_start) }, 
                    message,
                }
            };

            let (i, c) = self.chars.next().ok_or_else(|| error_maker(0, "unclosed string literal".to_string()))?;
            if c == '"' {
                break i + 1;
            }
            if c == '\n' {
                self.line += 1;
                self.line_start = i;
            }
            let added = if c == '\\' {
                match self.chars.next().ok_or_else(|| error_maker(i, "expected escaped character after backslash".to_string()))?.1 {
                    'n' => '\n',
                    't' => '\t',
                    '\\' => '\\',
                    '"' => '"',
                    '\'' => '\'', // huh? why would we need to escape this?
                    f@'0'..='9' => {
                        let (_, s) = self.chars.next().ok_or_else(|| error_maker(i, "expected second escaped number".to_string()))?;
                        let (_, t) = self.chars.next().ok_or_else(|| error_maker(i, "expected third escaped number".to_string()))?;
                        if !matches!((s, t), ('0'..='9', '0'..='9')) {
                            return Err(error_maker(i, "second and third escape characters muts be digits".to_string()));
                        }
                        let zero = '0' as u32;
                        let n = (f as u32 - zero) * 100
                            + (s as u32 - zero) * 10
                            + (t as u32 - zero) ;
                        if n > 255 {
                            return Err(error_maker(i, format!("illegal escaped character constant: {n}")));
                        }
                        // todo: guhH!?
                        // oat doesn't really support unicode, so should strings just be bytes
                        // instead?
                        char::from_u32(n).expect("valid unicode codepoint")
                    }
                    c => return Err(error_maker(i, format!("unrecocgnized escape character: '{c}'"))),
                }
            } else {
                c
            };
            contents.push(added);
        };

        Ok(Token {
            loc: Range { 
                start: (start_line, start_col),
                end: (self.line, end - self.line_start),
            },
            kind: TokenKind::String,
            data: TokenData::String(self.arena.intern_string(contents)),
        })
    }

    pub fn lex(&mut self) -> Result<Token<'output>, LexerError> {
        loop {
            let token = match self.chars.peek().map(|(_, c)| c) {
                Some(' ' | '\t' | '\n') => {
                    let (i, c) = self.chars.next().unwrap();
                    if c == '\n' {
                        self.line += 1;
                        self.line_start = i;
                    }
                    continue;
                }
                Some('.') => self.single(TokenKind::Dot),
                Some(';') => self.single(TokenKind::Semi),
                Some(',') => self.single(TokenKind::Comma),
                Some('{') => self.single(TokenKind::LBrace),
                Some('}') => self.single(TokenKind::RBrace),
                Some('+') => self.single(TokenKind::Plus),
                Some('-') => self.maybe_double(TokenKind::Dash, '>', TokenKind::Arrow),
                Some('*') => self.single(TokenKind::Star),
                Some('=') => self.maybe_double(TokenKind::Eq, '=', TokenKind::EqEq),
                Some('!') => self.maybe_double(TokenKind::Bang, '=', TokenKind::BangEq),
                Some('(') => self.single(TokenKind::LParen),
                Some(')') => self.single(TokenKind::RParen),
                Some('<') => {
                    let (i, _) = self.chars.next().unwrap();
                    let (kind, len) = match self.chars.peek() {
                        Some((_, '<')) => {
                            self.chars.next().unwrap();
                            (TokenKind::LtLt, 2)
                        }
                        Some((_, '=')) => {
                            self.chars.next().unwrap();
                            (TokenKind::LtEq, 2)
                        }
                        _ => (TokenKind::Lt, 1)
                    };
                    Token::one_line(kind, self.line, i, len, TokenData::None)
                }
                Some('>') => {
                    let (i, _) = self.chars.next().unwrap();
                    let (kind, len) = match self.chars.peek() {
                        Some((_, '>')) => {
                            self.chars.next().unwrap();
                            match self.chars.peek() {
                                Some((_, '>')) => {
                                    self.chars.next().unwrap();
                                    (TokenKind::GtGtGt, 3)
                                }
                                _ => (TokenKind::GtGt, 2),
                            }
                        }
                        Some((_, '=')) => {
                            self.chars.next().unwrap();
                            (TokenKind::GtEq, 2)
                        }
                        _ => (TokenKind::Gt, 1)
                    };
                    Token::one_line(kind, self.line, i, len, TokenData::None)
                }
                Some('&') => self.single(TokenKind::Amper),
                Some('|') => self.single(TokenKind::Bar),
                Some('~') => self.single(TokenKind::Tilde),
                Some('?') => self.single(TokenKind::Question),
                Some(']') => self.single(TokenKind::RBracket),
                Some('[') => {
                    let (i, _) = self.chars.next().unwrap();
                    let (kind, mut len) = match self.chars.peek() {
                        Some((_, '&')) => {
                            self.chars.next().unwrap();
                            (TokenKind::IAnd, 2)
                        }
                        Some((_, '|')) => {
                            self.chars.next().unwrap();
                            (TokenKind::IOr, 2)
                        }
                        _ => (TokenKind::LBracket, 1)
                    };
                    if len == 2 {
                        let (_, c) = self.chars.next().unwrap();
                        if c != ']' {
                            panic!("what the hell! i wanted a ']' not a {c}");
                        }
                        len += 1;
                    }
                    Token::one_line(kind, self.line, i, len, TokenData::None)
                }
                Some('0'..='9') => self.integer()?,
                Some('a'..='z') => self.ident(),
                Some('A'..='Z') => self.uident(),
                Some('"') => self.string()?,
                Some('#') => {
                    let (i, _) = self.chars.peek().unwrap();
                    let msg = if *i == self.line_start {
                        "directives are unimplemented".to_string()
                    } else {
                        "directives must be the first thing on the line".to_string()
                    };
                    return Err(LexerError {
                        location: Range {  
                            start: (self.line, *i),
                            end: (self.line, i+1),
                        },
                        message: msg,
                    });
                }
                Some('/') => {
                    let (start_col, _) = self.chars.next().unwrap();
                    let start_line = self.line;
                    let error_maker = |e_line, e_col, message| LexerError {
                        location: Range { start: (start_line, start_col), end: (e_line, e_col) },
                        message,
                    };

                    self.chars.next().filter(|(_, c)| *c == '*').ok_or_else(|| error_maker(self.line, start_col + 1 - self.line_start, "expected '*' after '/' to start a comment block".to_string()))?;
                    let mut level = 1;
                    while level > 0 {
                        let (i1, c) = self.chars.next().ok_or_else(|| error_maker(self.line, start_col + 1 - self.line_start, "uclosed comment".to_string()))?;
                        if c == '*' {
                            let (_, c2) = self.chars.next().ok_or_else(|| error_maker(self.line, i1 - self.line_start, "uclosed comment".to_string()))?;
                            if c2 == '/' {
                                level -= 1;
                                self.chars.next();
                            }
                        } else if c == '/' {
                            let (_, c2) = self.chars.next().ok_or_else(|| error_maker(self.line, i1 - self.line_start, "uclosed comment".to_string()))?;
                            if c2 == '*' {
                                level += 1;
                                self.chars.next();
                            }
                        } else if c == '\n' {
                            self.line += 1;
                            self.line_start = i1;
                        }
                    }
                    continue;
                }
                None => Token {
                    kind: TokenKind::Eof,
                    loc: Range { start: (0, 0), end: (0, 0) },
                    data: TokenData::None,
                },
                Some(_) => {
                    let (i, c) = self.chars.peek().unwrap();
                    return Err(LexerError {
                        location: Range {
                            start: (self.line, i - self.line_start),
                            end: (self.line, i + 1- self.line_start),
                        },
                        message: format!("unrecognized character {c}"),
                    });
                }
            };

            return Ok(token);
        }
    }

    pub fn lex_all(&mut self) -> Result<Vec<Token<'output>>, LexerError> {
        let mut tokens = Vec::new();
        loop {
            let t = self.lex()?;
            tokens.push(t);
            if t.kind == TokenKind::Eof {
                break;
            }
        }
        Ok(tokens)
    }
}
