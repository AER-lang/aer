//! Diagnostic types produced by the ÆR lexer

use crate::token::Span;

/// The severity of a lexer diagnostic
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    /// The token is malformed but the lexer could produce a reasonable
    /// best-effort result (e.g. an integer with an unknown suffix)
    Warning,
    /// The token cannot be represented correctly.
    /// The lexer recovered by emitting TokenKind::Unknown or a partial token
    Error,
}
