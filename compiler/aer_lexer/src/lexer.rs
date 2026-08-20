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
}
