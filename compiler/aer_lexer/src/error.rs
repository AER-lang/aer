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

/// A diagnostic message produced during lexing
///
/// The lexer never panics: It always produces some token stream and
/// accumulates errors here. The driver decides whether to abort or continue
#[derive(Debug, Clone, PartialEq)]
pub struct LexError {
    pub severity: Severity,
    pub span: Span,
    pub message: String,
}

impl LexError {
    pub fn error(span: Span, message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Error,
            span,
            message: message.into(),
        }
    }

    pub fn warning(span: Span, message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Warning,
            span,
            message: message.into(),
        }
    }
}
