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
