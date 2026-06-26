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

impl TokenKind {
    /// Human-readable name used in error messages.
    pub fn description(&self) -> &'static str {
        match self {
            Self::IntLit(_)    => "integer literal",
            Self::FloatLit(_)  => "float literal",
            Self::BoolLit(_)   => "boolean literal",
            Self::StringLit(_) => "string literal",
            Self::CharLit(_)   => "character literal",
            Self::Ident        => "identifier",

            Self::KwAsync    => "`async`",
            Self::KwAwait    => "`await`",
            Self::KwBreak    => "`break`",
            Self::KwComptime => "`comptime`",
            Self::KwConst    => "`const`",
            Self::KwContinue => "`continue`",
            Self::KwDefer    => "`defer`",
            Self::KwDyn      => "`dyn`",
            Self::KwElse     => "`else`",
            Self::KwEnum     => "`enum`",
            Self::KwExtern   => "`extern`",
            Self::KwFalse    => "`false`",
            Self::KwFn       => "`fn`",
            Self::KwFor      => "`for`",
            Self::KwIf       => "`if`",
            Self::KwImpl     => "`impl`",
            Self::KwIn       => "`in`",
            Self::KwLet      => "`let`",
            Self::KwLoop     => "`loop`",
            Self::KwMatch    => "`match`",
            Self::KwMod      => "`mod`",
            Self::KwMove     => "`move`",
            Self::KwMut      => "`mut`",
            Self::KwNull     => "`null`",
            Self::KwPub      => "`pub`",
            Self::KwReturn   => "`return`",
            Self::KwSelf     => "`self`",
            Self::KwSelfType => "`Self`",
            Self::KwStruct   => "`struct`",
            Self::KwTrait    => "`trait`",
            Self::KwTrue     => "`true`",
            Self::KwType     => "`type`",
            Self::KwUnsafe   => "`unsafe`",
            Self::KwUse      => "`use`",
            Self::KwWhere    => "`where`",
            Self::KwWhile    => "`while`",

            Self::KwBool     => "`bool`",
            Self::KwI8       => "`i8`",
            Self::KwI16      => "`i16`",
            Self::KwI32      => "`i32`",
            Self::KwI64      => "`i64`",
            Self::KwI128     => "`i128`",
            Self::KwU8       => "`u8`",
            Self::KwU16      => "`u16`",
            Self::KwU32      => "`u32`",
            Self::KwU64      => "`u64`",
            Self::KwU128     => "`u128`",
            Self::KwIsize    => "`isize`",
            Self::KwUsize    => "`usize`",
            Self::KwF32      => "`f32`",
            Self::KwF64      => "`f64`",
            Self::KwStr      => "`str`",
            Self::KwVoid     => "`void`",
            Self::KwNoreturn => "`noreturn`",

            Self::LParen     => "`(`",
            Self::RParen     => "`)`",
            Self::LBracket   => "`[`",
            Self::RBracket   => "`]`",
            Self::LBrace     => "`{`",
            Self::RBrace     => "`}`",

            Self::Comma      => "`,`",
            Self::Semicolon  => "`;`",
            Self::Colon      => "`:`",
            Self::ColonColon => "`::`",
            Self::Dot        => "`.`",
            Self::DotDot     => "`..`",
            Self::DotDotDot  => "`...`",
            Self::DotDotEq   => "`..=`",
            Self::Arrow      => "`->`",
            Self::FatArrow   => "`=>`",
            Self::Question   => "`?`",
            Self::Bang       => "`!`",
            Self::At         => "`@`",
            Self::Hash       => "`#`",
            Self::Amp        => "`&`",
            Self::AmpAmp     => "`&&`",
            Self::Pipe       => "`|`",
            Self::PipePipe   => "`||`",
            Self::Caret      => "`^`",
            Self::Tilde      => "`~`",

            Self::Eq         => "`=`",
            Self::EqEq       => "`==`",
            Self::BangEq     => "`!=`",
            Self::Lt         => "`<`",
            Self::LtEq       => "`<=`",
            Self::Gt         => "`>`",
            Self::GtEq       => "`>=`",
            Self::LtLt       => "`<<`",
            Self::GtGt       => "`>>`",

            Self::Plus       => "`+`",
            Self::PlusEq     => "`+=`",
            Self::Minus      => "`-`",
            Self::MinusEq    => "`-=`",
            Self::Star       => "`*`",
            Self::StarEq     => "`*=`",
            Self::Slash      => "`/`",
            Self::SlashEq    => "`/=`",
            Self::Percent    => "`%`",
            Self::PercentEq  => "`%=`",
            Self::AmpEq      => "`&=`",
            Self::PipeEq     => "`|=`",
            Self::CaretEq    => "`^=`",
            Self::LtLtEq     => "`<<=`",
            Self::GtGtEq     => "`>>=`",

            Self::Eof        => "<end of file>",
            Self::Unknown    => "<unknown>",
        }
    }
}
