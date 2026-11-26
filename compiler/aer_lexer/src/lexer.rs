//! Hand-written ÆR lexer
//!
//! Design goals (in priority order):
//!     1 - Correctness - Every valid toke is produced correctly
//!     2 - Good errors - Malformed tokens get a precise span and useful message
//!     3 - Recovery - After an error the lexer continues, it never panics
//!     4 - Speed - Single-pass, zero allocations except for strin/char literal bodies
//!
//! The lexer ir a cursor over raw UTF-8 bytes with a one-character lookahead
//! All offsets are byte offsets into the original source string

use crate::error::LexError;
use crate::token::{Span, Token, TokenKind};

// ── Cursor ───────────────────────────────────────────────────────────────────

// Low level byte cursor over a UTF-8 source string
struct Cursor<'src> {
    src: &'src str,
    /// Current position (byte offset)
    pos: usize,
}

impl<'src> Cursor<'src> {
    fn new(src: &'src str) -> Self {
        Self { src, pos: 0 }
    }

    /// Is the cursor at the end of the input?
    #[inline]
    fn is_eof(&self) -> bool {
        self.bos >= self.src.len()
    }

    /// The byte at the current position without advancing (resturns \0 at EOF)
    #[inline]
    fn peek(&self) -> char {
        self.src[self.pos..].chars().next().unwrap_or('\0')
    }

    /// The byte one position ahead (returns \0 if out of bounds)
    #[inline]
    fn peek2(&self) -> char {
        let mut chars = self.src[self.pos..].chars();
        chars.next(); // Skip current
        chars.next().unwrap_or('\0')
    }

    /// Advance past the current character and return it
    #[inline]
    fn advance(&mut self) -> char {
        let ch = self.peek();
        self.pos += ch.len_utf8();
        ch
    }

    /// Advance onl if the curent char equals expected. Returns true if it did
    #[inline]
    fn eat(&mut self, expected: char) -> bool {
        if self.peek() == expected {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Advance while pred holds
    #[inline]
    fn eat_while(&mut self, mut pred: impl FnMut(char) -> bool) {
        while !self.is_eof() && pred(self.peek()) {
            self.advance();
        }
    }

    /// Current position as u32 (safe: source files must be < 4 GB)
    #[inline]
    fn pos32(&self) -> u32 {
        self.pos as u32
    }
}

// ── Keyword table ─────────────────────────────────────────────────────────────

fn keyword(s: &str) -> Option<TokenKind> {
    Some(match s {
        "async"    => TokenKind::KwAsync,
        "await"    => TokenKind::KwAwait,
        "break"    => TokenKind::KwBreak,
        "comptime" => TokenKind::KwComptime,
        "const"    => TokenKind::KwConst,
        "continue" => TokenKind::KwContinue,
        "defer"    => TokenKind::KwDefer,
        "dyn"      => TokenKind::KwDyn,
        "else"     => TokenKind::KwElse,
        "enum"     => TokenKind::KwEnum,
        "extern"   => TokenKind::KwExtern,
        "false"    => TokenKind::KwFalse,
        "fn"       => TokenKind::KwFn,
        "for"      => TokenKind::KwFor,
        "if"       => TokenKind::KwIf,
        "impl"     => TokenKind::KwImpl,
        "in"       => TokenKind::KwIn,
        "let"      => TokenKind::KwLet,
        "loop"     => TokenKind::KwLoop,
        "match"    => TokenKind::KwMatch,
        "mod"      => TokenKind::KwMod,
        "move"     => TokenKind::KwMove,
        "mut"      => TokenKind::KwMut,
        "null"     => TokenKind::KwNull,
        "pub"      => TokenKind::KwPub,
        "return"   => TokenKind::KwReturn,
        "self"     => TokenKind::KwSelf,
        "Self"     => TokenKind::KwSelfType,
        "struct"   => TokenKind::KwStruct,
        "trait"    => TokenKind::KwTrait,
        "true"     => TokenKind::KwTrue,
        "type"     => TokenKind::KwType,
        "unsafe"   => TokenKind::KwUnsafe,
        "use"      => TokenKind::KwUse,
        "where"    => TokenKind::KwWhere,
        "while"    => TokenKind::KwWhile,

        "bool"     => TokenKind::KwBool,
        "i8"       => TokenKind::KwI8,
        "i16"      => TokenKind::KwI16,
        "i32"      => TokenKind::KwI32,
        "i64"      => TokenKind::KwI64,
        "i128"     => TokenKind::KwI128,
        "u8"       => TokenKind::KwU8,
        "u16"      => TokenKind::KwU16,
        "u32"      => TokenKind::KwU32,
        "u64"      => TokenKind::KwU64,
        "u128"     => TokenKind::KwU128,
        "isize"    => TokenKind::KwIsize,
        "usize"    => TokenKind::KwUsize,
        "f32"      => TokenKind::KwF32,
        "f64"      => TokenKind::KwF64,
        "str"      => TokenKind::KwStr,
        "void"     => TokenKind::KwVoid,
        "noreturn" => TokenKind::KwNoreturn,

        _ => return None,
    })
}

// ── Lexer ─────────────────────────────────────────────────────────────────────

/// The main ÆR lexer
///
/// Call [Lexer::tokenize] to lex an entire source file at once, or use
/// [Lexer::next_token] for on-demand streaming
pub struct Lexer<'src> {
    cursor: Cursor<'src>,
    errors: Vec<LexError>,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer from a source string
    pub fn new(src: &'src str) -> Self {
        Self {
            cursor: Cursor::new(src),
            errors: Vec::new(),
        }
    }

    /// Lex the entire source and return all tokens (including the final Eof
    /// sentinel) plus any accumulated diagnostics
    pub fn tokenize(mut self) -> (Vec<Token>, Vec<LexError>) {
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token();
            let is_eof = tok.is_eof();
            tokens.push(tok);
            if is_eof {
                break;
            }
        }
        (tokens, self.errors)
    }

    /// Lex the next token, skipping whitespace and comments
    pub fn next_token(&mut self) -> Token {
        self.skip_trivia();

        if self.cursor.is_eof() {
            let pos = self.cursor.pos32();
            return Token::new(TokenKind::Eof, Span::new(pos, pos));
        }

        let start = self.cursor.pos32();
        let ch = self.cursor.advance();
        let kind = self.lex_token(ch, start);
        let end = self.cursor.pos32();
        Token::new(kind, Span::new(start, end))
    }

    // ── Trivia ────────────────────────────────────────────────────────────────

    /// Skip whitespace and comments (both // and /* */)
    fn skip_trivia(&mut self) {
        loop {
            // Whitespace
            self.cursor.eat_while(|c| c.is_ascii_whitespace());
            if self.cursor.is_eof() {
                break;
            }

            // Line comment
            if self.cursor.peek() == '/' && self.cursor.peek2() == '/' {
                self.cursor.eat_while(|c| c != '\n');
                continue;
            }

            // Block comment (non-nesting, per spec)
            if self.cursor.peek() == '/' && self.cursor.peek2() == '*' {
                let start = self.cursor.pos32();
                self.cursor.advance(); // /
                self.cursor.advance(); // *
                loop {
                    if self.cursor.is_eof() {
                        self.errors.push(LexError::error(
                            Span::new(start, self.cursor.pos32()),
                            "unterminated block comment",
                        ));
                        break;
                    }
                    if self.cursor.peek() == '*' && self.cursor.peek2() == '/' {
                        self.cursor.advance(); // *
                        self.cursor.advance(); // /
                        break;
                    }
                    self.cursor.advance();
                }
                continue;
            }

            break;
        }
    }

    // ── Token dispatch ────────────────────────────────────────────────────────

    fn lex_token(&mut self, ch: char, start: u32) -> TokenKind {
        match ch {
            // Grouping
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,

            // Single-char or disambiguated punctuation
            ',' => TokenKind::Comma,
            ';' => TokenKind::Semicolon,
            '~' => TokenKind::Tilde,
            '@' => TokenKind::At,
            '#' => TokenKind::Hash,

            // Colon / ::
            ':' => {
                if self.cursor.eat(':') { TokenKind::ColonColon }
                else { TokenKind::Colon }
            }

            // Dot / .. / ... / ..=
            '.' => {
                if self.cursor.eat('.') {
                    if self.cursor.eat('.') { TokenKind::DotDotDot }
                    else if self.cursor.eat('=') { TokenKind::DotDotEq }
                    else { TokenKind::DotDot }
                } else {
                    // Could be the start of a float like .5 — not supported in
                    // ÆR (floats must have a digit before the dot). Plain dot
                    TokenKind::Dot
                }
            }

            // Arrow / minus / -=
            '-' => {
                if self.cursor.eat('>') { TokenKind::Arrow }
                else if self.cursor.eat('=') { TokenKind::MinusEq }
                else { TokenKind::Minus }
            }

            // Fat arrow / ==/ =
            '=' => {
                if self.cursor.eat('>') { TokenKind::FatArrow }
                else if self.cursor.eat('=') { TokenKind::EqEq }
                else { TokenKind::Eq }
            }

            // ! / !=
            '!' => {
                if self.cursor.eat('=') { TokenKind::BangEq }
                else { TokenKind::Bang }
            }

            // < / <= / << / <<=
            '<' => {
                if self.cursor.eat('<') {
                    if self.cursor.eat('=') { TokenKind::LtLtEq }
                    else { TokenKind::LtLt }
                } else if self.cursor.eat('=') { TokenKind::LtEq }
                else { TokenKind::Lt }
            }

            // > / >= / >> / >>=
            '>' => {
                if self.cursor.eat('>') {
                    if self.cursor.eat('=') { TokenKind::GtGtEq }
                    else { TokenKind::GtGt }
                } else if self.cursor.eat('=') { TokenKind::GtEq }
                else { TokenKind::Gt }
            }

            // + / +=
            '+' => {
                if self.cursor.eat('=') { TokenKind::PlusEq }
                else { TokenKind::Plus }
            }

            // * / *=
            '*' => {
                if self.cursor.eat('=') { TokenKind::StarEq }
                else { TokenKind::Star }
            }

            // / / /=  (comments already consumed in skip_trivia)
            '/' => {
                if self.cursor.eat('=') { TokenKind::SlashEq }
                else { TokenKind::Slash }
            }

            // % / %=
            '%' => {
                if self.cursor.eat('=') { TokenKind::PercentEq }
                else { TokenKind::Percent }
            }

            // & / &= / &&
            '&' => {
                if self.cursor.eat('&') { TokenKind::AmpAmp }
                else if self.cursor.eat('=') { TokenKind::AmpEq }
                else { TokenKind::Amp }
            }

            // | / |= / ||
            '|' => {
                if self.cursor.eat('|') { TokenKind::PipePipe }
                else if self.cursor.eat('=') { TokenKind::PipeEq }
                else { TokenKind::Pipe }
            }

            // ^ / ^=
            '^' => {
                if self.cursor.eat('=') { TokenKind::CaretEq }
                else { TokenKind::Caret }
            }

            // ? (error propagation)
            '?' => TokenKind::Question,

            // String literal
            '"' => self.lex_string(start),

            // Character literal
            '\'' => self.lex_char(start),

            // Number
            c if c.is_ascii_digit() => self.lex_number(c, start),

            // Identifier or keyword
            c if is_ident_start(c) => self.lex_ident(c, start),

            // Anything else
            _ => {
                self.errors.push(LexError::error(
                    Span::new(start, self.cursor.pos32()),
                    format!("unexpected character {:?}", ch),
                ));
                TokenKind::Unknown
            }
        }
    }

    // ── Identifiers & keywords ─────────────────────────────────────────────────

    fn lex_ident(&mut self, first: char, start: u32) -> TokenKind {
        let _ = first; // Already consumed
        self.cursor.eat_while(is_ident_continue);
        let end = self.cursor.pos32();
        let text = &self.cursor.src[start as usize..end as usize];
        keyword(text).unwrap_or(TokenKind::Ident)
    }
    
    // ── Numbers ───────────────────────────────────────────────────────────────

    fn lex_number(&mut self, first: char, start: u32) -> TokenKind {
        // Detect base prefix (0x, 0b, 0o)
        if first == '0' {
            match self.cursor.peek() {
                'x' | 'X' => {
                    self.cursor.advance();
                    return self.lex_int_radix(start, 16, "hex");
                }
                'b' | 'B' => {
                    self.cursor.advance();
                    return self.lex_int_radix(start, 2, "binary");
                }
                'o' | 'O' => {
                    self.cursor.advance();
                    return self.lex_int_radix(start, 8, "octal");
                }
                _ => {}
            }
        }

        // Decimal: Consume remaining digits (with optional _ separators)
        self.cursor.eat_while(|c| c.is_ascii_digit() || c == '_');

        // Float if we see .digit or e/E
        let is_float = (self.cursor.peek() == '.' && self.cursor.peek2().is_ascii_digit())
            || matches!(self.cursor.peek(), 'e' | 'E');

        if is_float {
            return self.lex_float(start);
        }

        // Parse integer value (ignore _ separators)
        let raw = &self.cursor.src[start as usize..self.cursor.pos as usize];
        // Consume optional type suffix (i32, u64, etc.)
        self.eat_int_suffix();

        let digits: String = raw.chars().filter(|&c| c != '_').collect();
        match u128::from_str_radix(&digits, 10) {
            Ok(v) => TokenKind::IntLit(v),
            Err(_) => {
                self.errors.push(LexError::error(
                    Span::new(start, self.cursor.pos32()),
                    "integer literal too large",
                ));
                TokenKind::Unknown
            }
        }
    }

    fn lex_int_radix(&mut self, start: u32, radix: u32, name: &str) -> TokenKind {
        let digits_start = self.cursor.pos;
        self.cursor.eat_while(|c| c.is_ascii_alphanumeric() || c == '_');
        let digits_end = self.cursor.pos;

        if digits_start == digits_end {
            self.errors.push(LexError::error(
                Span::new(start, self.cursor.pos32()),
                format!("empty {} literal", name),
            ));
            return TokenKind::Unknown;
        }

        self.eat_int_suffix();

        let raw = &self.cursor.src[digits_start..digits_end];
        let digits: String = raw.chars().filter(|&c| c != '_').collect();
        match u128::from_str_radix(&digits, radix) {
            Ok(v) => TokenKind::IntLit(v),
            Err(_) => {
                self.errors.push(LexError::error(
                    Span::new(start, self.cursor.pos32()),
                    format!("invalid {} literal", name),
                ));
                TokenKind::Unknown
            }
        }
    }
}
