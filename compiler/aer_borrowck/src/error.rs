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

    pub fn message(&self) -> String {
        match &self.kind {
            BorrowErrorKind::UseAfterMove { name, moved_at } =>
                format!(
                    "use of moved value `{}`; value was moved at {}",
                    name, moved_at
                ),
            BorrowErrorKind::MoveWhileBorrowed { name, borrow_span } =>
                format!(
                    "cannot move `{}` because it is borrowed (borrow at {})",
                    name, borrow_span
                ),
            BorrowErrorKind::ConflictingBorrow { place, existing_kind, existing_span, new_kind } =>
                format!(
                    "cannot borrow `{}` as {} because it is already borrowed as {} at {}",
                    place, new_kind.as_str(), existing_kind.as_str(), existing_span
                ),
            BorrowErrorKind::MutationOfImmutable { name } =>
                format!("cannot assign to `{}`, which is not declared `mut`", name),
            BorrowErrorKind::RefMutOfImmutable { name } =>
                format!(
                    "cannot borrow `{}` as mutable, as it is not declared with `mut`",
                    name
                ),
            BorrowErrorKind::BorrowOutlivesData { borrow_span, data_span } =>
                format!(
                    "borrow (created at {}) does not live long enough; \
                     borrowed data (declared at {}) is dropped first",
                    borrow_span, data_span
                ),
            BorrowErrorKind::UseAfterDrop { name } =>
                format!("use of `{}` after it has been dropped", name),
        }
    }
}

impl std::fmt::Display for BorrowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[borrow error] {}: {}", self.span, self.message())
    }
}
