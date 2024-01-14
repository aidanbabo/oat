use super::Range;

use std::iter::Peekable;
use std::str::CharIndices;
use std::collections::HashMap;

use once_cell::sync::Lazy;

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

#[derive(Clone, Debug)]
pub struct Token {
    pub loc: Range,
    pub kind: TokenKind,
    pub data: TokenData,
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, enum_map::Enum)]
pub enum TokenKind {
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

#[derive(Clone, Debug)]
pub enum TokenData {
    Int(i64),
    String(String),
    None,
}

impl Token {
    fn one_line(kind: TokenKind, line: usize, start: usize, len: usize, data: TokenData) -> Token {
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

pub struct Lexer<'input> {
    input: &'input str,
    line: usize,
    line_start: usize,
    chars: Peekable<CharIndices<'input>>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Self {
            input,
            line: 1,
            line_start: 0,
            chars: input.char_indices().peekable(),
        }
    }

    fn single(&mut self, kind: TokenKind) -> Token {
        let (i, _) = self.chars.next().unwrap();
        Token::one_line(kind, self.line, i - self.line_start, 1, TokenData::None)
    }

    fn maybe_double(&mut self, single_kind: TokenKind, second_char: char, double_kind: TokenKind) -> Token {
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

    fn integer(&mut self) -> Token {
        let mut num = 0i64;
        let (start, c0) = self.chars.next().unwrap();
        let mut end = start;
        let mut hex = false;
        if c0 == '0' {
            match self.chars.peek() {
                Some((_, 'x')) => {
                    end = self.chars.next().unwrap().0;
                    hex = true;
                }
                _ => {},
            }
        } else {
            num = c0 as i64 - '0' as i64
        }

        let multiplier = if hex { 16 } else { 10 };
        let mut c;
        loop {
            match self.chars.peek().map(|(_, c)| c) {
                Some('0'..='9') => {
                    (end, c) = self.chars.next().unwrap();
                    num = num * multiplier + (c as i64 - '0' as i64);
                }
                Some('a'..='f') => {
                    (end, c) = self.chars.next().unwrap();
                    num = num * multiplier + (c as i64 - 'a' as i64 + 10 );
                }
                Some('A'..='F') => {
                    (end, c) = self.chars.next().unwrap();
                    num = num * multiplier + (c as i64 - 'A' as i64 + 10 );
                }
                _ => break,
            }
        }

        Token::one_line(TokenKind::IntLit, self.line, start - self.line_start, end + 1 - start, TokenData::Int(num))
    }

    fn any_ident(&mut self) -> (usize, usize) {
        let (start, _) = self.chars.next().unwrap();
        let mut end = start;
        loop {
            match self.chars.peek().map(|(_, c)| c) {
                Some('a'..='z' | 'A'..='Z' | '_' | '0'..='9') => {
                    end = self.chars.next().unwrap().0;
                }
                _ => break,
            }
        }
        end += 1;
        (start, end)
    }

    fn uident(&mut self) -> Token {
        let (start, end) = self.any_ident();
        let s = &self.input[start..end];
        Token::one_line(TokenKind::UIdent, self.line, start - self.line_start, end - start, TokenData::String(s.to_string()))
    }

    fn ident(&mut self) -> Token {
        let (start, mut end) = self.any_ident();
        let s = &self.input[start..end];
        let kind = if let Some(kind) = KEYWORDS.get(s) {
            match self.chars.peek().map(|(_, c)| c) {
                Some('?') if *kind == TokenKind::If => {
                    self.chars.next().unwrap();
                    end += 1;
                    TokenKind::Ifq
                }
                _ => kind.clone(),
            }
        } else {
            TokenKind::Ident
        };
        Token::one_line(kind, self.line, start - self.line_start, end - start, TokenData::String(s.to_string()))
    }

    fn string(&mut self) -> Token {
        let (start, _) = self.chars.next().unwrap();
        let start_line = self.line;
        let start_col = start - self.line_start;
        let end = loop {
            let Some((i, c)) = self.chars.next() else { panic!("unclosed string literal") };
            if c == '"' {
                break i + 1;
            }
            if c == '\n' {
                self.line += 1;
                self.line_start = i;
            }
            if c == '\\' {
                // escape sequence handling is dealt with later
                self.chars.next();
            }
        };

        let contents = escape_string(&self.input[start..end]);
        Token {
            loc: Range { 
                start: (start_line, start_col),
                end: (self.line, end - self.line_start),
            },
            kind: TokenKind::String,
            data: TokenData::String(contents.to_string()),
        }
    }

    pub fn lex(&mut self) -> Option<Token> {
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
                Some('0'..='9') => self.integer(),
                Some('a'..='z') => self.ident(),
                Some('A'..='Z') => self.uident(),
                Some('"') => self.string(),
                None => return None,
                _ => todo!(),
            };

            return Some(token);
        }
    }

    pub fn lex_all(&mut self) -> Vec<Token> {
        std::iter::from_fn(|| self.lex()).collect()
    }
}

