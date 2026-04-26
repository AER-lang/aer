//! Diagnostic types produced by the ÆR borrow checker

use aer_lexer::Span;

#[derive(Debug, Clone)]
pub struct BorrowError {
    pub span:    Span,
    pub kind:    BorrowErrorKind,
}

#[derive(Debug, Clone)]
pub enum BorrowErrorKind {
    /// A value was used after it was moved
    UseAfterMove {
        name:   String,
        move_at: Span,
    },
    /// A value was moved while it was borrowed
    MoveWhiteBorrowed {
        name:       String,
        borrow_span: Span,
    },
    /// An exclusive borrow (&mut) conflicts with an existing borrow
    ConflictingBorrow {
        place:          String,
        existing_kind:  BorrowKind,
        existing_span:  Span,
        new_kind:       BorrowKind,
    },
    /// Tried to mutate an immutable binding
    MutationOfImmutable {
        name: String,
    },
    /// Tried to take &mut of an immutable binding
    RefMutOfImmutable {
        name: String,
    },
    /// A borrow's lifetime exceeded the lifetime of the borrowed place
    BorrowOutlivesData {
        borrow_span: Span,
        data_span:   Span,
    },
    /// A value was used after it was dropped / storage ended
    UseAfterDrop {
        name: String,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BorrowKind {
    Shared,    // &T
    Exclusive, // &mut T
}

impl BorrowKind {
    pub fn as_str(self) -> &'static str {
        match self { Self::Shared => "&", Self::Exclusive => "&mut" }
    }
}

impl BorrowError {
    pub fn new(span: Span, kind: BorrowErrorKind) -> Self {
        Self { span, kind }
    }
}
