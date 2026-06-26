//! Token definitions for the ÆR lexer
//!
//! Every token carries its source span so that later compiler passes
//! can produce precise error messages without re-parsing

// ── Span ────────────────────────────────────────────────────────────────────

/// A byte-offset range within a single source file
///
/// start is inclusive, end is exclusive (like Rust ranges)
/// Both offsets are measured from the beginning of the source string
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    #[inline]
    pub fn new(start: u32, end: u32) -> Self {
        debug_assert!(start <= end, "Span start must be <= end");
        Self { start, end }
    }

    /// The number of bytes covered by this span
    #[inline]
    pub fn len(self) -> u32 {
        self.end - self.start
    }

    #[inline]
    pub fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// Extend this span to also cover other
    #[inline]
    pub fn merge(self, other: Span) -> Span {
        Span::new(self.start.min(other.start), self.end.max(other.end))
    }

    /// Return the slice of src covered by this span
    #[inline]
    pub fn slice<'src>(self, src: &'src str) -> &'src str {
        &src[self.start as usize..self.end as usize]
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

// ── Token kinds ─────────────────────────────────────────────────────────────

/// Every distinct kind of token the ÆR lexer can produce
///
/// Literals carry their parsed value so the parser never needs to re-parse.
/// Identifiers and unknown bytes carry no payload, use Span::slice on
/// the source string to recover the text
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // ── Literals ────────────────────────────────────────────────────────────
    /// An integer literal, e.g. 42, 0x2A, 0b101010, 0o52
    /// The value is the result of parsing, suffix (if any) is in Span
    IntLit(u128),

    /// A floating-point literal, e.g. 3.14, 1e-9, 0.5f32
    FloatLit(f64),

    /// A boolean literal: true or false
    BoolLit(bool),

    /// A string literal, e.g. "hello\nworld"
    /// The String contains the decoded content (escape sequences resolved)
    StringLit(String),

    /// A character literal, e.g. 'a', '\n'
    CharLit(char),

    // ── Identifier & keywords ────────────────────────────────────────────────
    /// A plain identifier that is not a keyword, e.g. foo, _bar, Point
    Ident,

    // Keywords - Listed alphabetically for easy scanning
    KwAsync,
    KwAwait,
    KwBreak,
    KwComptime,
    KwConst,
    KwContinue,
    KwDefer,
    KwDyn,
    KwElse,
    KwEnum,
    KwExtern,
    KwFalse,
    KwFn,
    KwFor,
    KwIf,
    KwImpl,
    KwIn,
    KwLet,
    KwLoop,
    KwMatch,
    KwMod,
    KwMove,
    KwMut,
    KwNull,
    KwPub,
    KwReturn,
    KwSelf,
    KwSelfType, // Self (capital)
    KwStruct,
    KwTrait,
    KwTrue,
    KwType,
    KwUnsafe,
    KwUse,
    KwWhere,
    KwWhile,

    // Built-in type keywords (could be plain identifiers but are reserved)
    KwBool,
    KwI8, KwI16, KwI32, KwI64, KwI128,
    KwU8, KwU16, KwU32, KwU64, KwU128,
    KwIsize, KwUsize,
    KwF32, KwF64,
    KwStr,
    KwVoid,
    KwNoreturn,

    // ── Punctuation ──────────────────────────────────────────────────────────
    /// "("
    LParen,
    /// ")"
    RParen,
    /// "["
    LBracket,
    /// "]"
    RBracket,
    /// "{"
    LBrace,
    /// "}"
    RBrace,

    /// ","
    Comma,
    /// ";"
    Semicolon,
    /// ":"
    Colon,
    /// "::"
    ColonColon,
    /// "."
    Dot,
    /// ".."
    DotDot,
    /// "..."
    DotDotDot,
    /// "..="
    DotDotEq,
    /// "->"
    Arrow,
    /// "=>"
    FatArrow,
    /// "?"
    Question,
    /// "!"
    Bang,
    /// "@"
    At,
    /// "#"
    Hash,
    /// "&"
    Amp,
    /// "&&"
    AmpAmp,
    /// "|"
    Pipe,
    /// "||"
    PipePipe,
    /// "^"
    Caret,
    /// "~"
    Tilde,

    // ── Operators ────────────────────────────────────────────────────────────
    /// "="
    Eq,
    /// "=="
    EqEq,
    /// "!="
    BangEq,
    /// "<"
    Lt,
    /// "<="
    LtEq,
    /// ">"
    Gt,
    /// ">="
    GtEq,
    /// "<<"
    LtLt,
    /// ">>"
    GtGt,

    /// "+"
    Plus,
    /// "+="
    PlusEq,
    /// "-"
    Minus,
    /// "-="
    MinusEq,
    /// "*"
    Star,
    /// "*="
    StarEq,
    /// "/"
    Slash,
    /// "/="
    SlashEq,
    /// "%"
    Percent,
    /// "%="
    PercentEq,
    /// "&="
    AmpEq,
    /// "|="
    PipeEq,
    /// "^="
    CaretEq,
    /// "<<="
    LtLtEq,
    /// ">>="
    GtGtEq,

    // ── Trivia & sentinels ───────────────────────────────────────────────────
    /// End of input
    Eof,

    /// A byte that could not be interpreted as the start of any valid token
    /// The lexer recovers and continues. The parser will emit an error
    Unknown,
}
