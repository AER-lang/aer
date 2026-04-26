//! Diagnostic types produced by the ÆR borrow checker

use aer_lexer::Span;

#[derive(Debug, Clone)]
pub struct BorrowError {
    pub span:    Span,
    pub kind:    BorrowErrorKind,
}

