//! Control Flow Graph (CFG) for the ÆR borrow checker
//! 
//! Design
//!
//! The borrow checker does not operato on the raw AST, that would make
//! liveness analysis very difficult the AST does not make control
//! flow edges explicit. Instead we lower each function body into a flag CFG:
//!
//! fn f(x: i32) -> i32 {
//!     let y = x + 1;          BB0: [Assign(y, x + 1), Goto(BB1)]
//!     if y > 0 {              BB1: [Branch(y > 0, BB2, BB3)]
//!         return y;           BB2: [Return(y)]
//!     }                       BB3: [Return(0)]
//!     return 0;
//! }
//!
//! Each basic block is a straight-line sequence of statement
//! followed by a single terminator that names the sucessor blocks
//!
//! Places
//!
//! A place is a path to a memory location: A local variable, possibly
//! projected through field accesses, index operations, or dereferences
//! Plane is kept minimal for this MVP, just the local and an optional chain of projections

use aer_lexer::Span;
use aer_tycheck::TypeId;

// ── Place ─────────────────────────────────────────────────────────────────────

/// A unique ID for a local variable (parameter or `let` binding) within a
/// single function body. IDs are allocated in declaration order
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LocalId(pub u32);

impl LocalId {
    pub const RETURN: LocalId = LocalId(0); // Conventional slot for the return value
}

impl std::fmt::Display for LocalId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 == 0 { write!(f, "_return") } else { write!(f, "_{}", self.0) }
    }
}

/// A projection step from one place to a sub-place.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Projection {
    /// `.field_name` — struct field access.
    Field(String),
    /// `[i]` — array/slice index (the index is not tracked precisely in MVP).
    Index,
    /// `*` — dereference.
    Deref,
}
