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

/// A memory location: A root local plus zero or more projections
///
/// Examples:
///
///     - x             → Place { root: id_of_x, proj: [] }
///     - p.x           → Place { root: id_of_p, proj: [Field("x")] }
///     - *ptr          → Place { root: id_of_ptr, proj: [Deref] }
///     - arr[0].name   → Place { root: id_of_arr, proj: [Index, Field("name")] }
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Place {
    pub root: LocalId,
    pub proj: Vec<Projection>,
}

impl Place {
    pub fn local(id: LocalId) -> Self {
        Self { root: id, proj: Vec::new() }
    }

    pub fn field(mut self, name: impl Into<String>) -> Self {
        self.proj.push(Projection::Field(name.into()));
        self
    }

    pub fn deref(mut self) -> Self {
        self.proj.push(Projection::Deref);
        self
    }

    /// True if this place is exactly a local variable (no projections)
    pub fn is_local(&self) -> bool {
        self.proj.is_empty()
    }

    /// True if other is a prefix of self (i.e. self is a sub-place of other)
    pub fn has_prefix(&self, other: &Place) -> bool {
        if self.root != other.root { return false; }
        if other.proj.len() > self.proj.len() { return false; }
        self.proj.starts_with(&other.proj)
    }
}

impl std::fmt::Display for Place {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.root)?;
        for p in &self.proj {
            match p {
                Projection::Field(n) => write!(f, ".{}", n)?,
                Projection::Index    => write!(f, "[_]")?,
                Projection::Deref    => write!(f, ".*")?,
            }
        }
        Ok(())
    }
}

// ── Rvalue / Operand ──────────────────────────────────────────────────────────

/// A simple value expression, the right-hand side of an assignment in the CFG
/// All complex expressions are decomposed into a sequence of these
#[derive(Debug, Clone)]
pub enum Rvalue {
    /// Use the value at a place (copy or move, depending on the type)
    Use(Operand),
    /// &place, shared borrow
    Ref(Place),
    /// &mut place, exclusive borrow
    RefMut(Place),
    /// A binary operation
    BinaryOp(BinOp, Operand, Operand),
    /// A unary operation
    UnaryOp(UnOp, Operand),
    /// Aggregate construction: Struct, tuple, or array
    Aggregate(AggregateKind, Vec<Operand>),
}

#[derive(Debug, Clone)]
pub enum Operand {
    /// Copy or move a place
    Move(Place),
    /// A constant value (literals, compile-time constants)
    Const(ConstVal),
}

#[derive(Debug, Clone)]
pub enum ConstVal {
    Int(u128),
    Float(f64),
    Bool(bool),
    Str(String),
    Void,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add, Sub, Mul, Div, Rem,
    BitAnd, BitOr, BitXor, Shl, Shr,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp { Neg, Not, Deref }

#[derive(Debug, Clone)]
pub enum AggregateKind {
    Tuple,
    Array,
    Struct(String),
}

// ── CFG Statements ────────────────────────────────────────────────────────────

/// A single statement inside a basic block
/// Each statement is straight-line, no branching
#[derive(Debug, Clone)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    /// place = rvalue
    Assign(Place, Rvalue),
    /// drop(place), explicit drop at end of scope
    Drop(Place),
    /// A storage-live annotation: the local is now in scope
    StorageLive(LocalId),
    /// A storage-dead annotation: the local is going out of scope
    StorageDead(LocalId),
    /// No-op, used as a placeholder after lowering errors
    Nop,
}

// ── Terminators ───────────────────────────────────────────────────────────────

#[derive(Debug,  Clone)]
pub struct Terminator {
    pub kind: TerminatorKind,
    pub span: span,
}

#[derive(Debug, Clone)]
pub enum TerminatorKind {
    /// Fall through to the single successor block
    Goto(BlockId),
    /// Conditional branch
    SwitchInt {
        /// The place holding the discriminant
        discriminant: Operand,
        /// (value, target) pairs, the last entry is the "otherwise" target
        targets: Vec<(u128, BlockId)>,
        otherwise: BlockId,
    },
    /// Function return
    Return,
    /// Unreachable (after loop {} with no break, or noreturn calls)
    Unreachable,
    Call {
        func: Operand,
        args: Vec<Operand>,
        /// Where to write the return value, and which block to go to after
        destination: Option<(Place, BlockId)>,
    },
    /// drop + goto (used for values with destructors at scope exit)
    DropAndGoto { place: Place, target: BlockId },
}

impl TerminatorKind {
    /// The successor blocks of this terminator
    pub fn successors(&self) -> Vec<BlockId> {
        match self {
            Self::Goto(b)                        => vec![*b],
            Self::SwitchInt { targets, otherwise, .. } => {
                let mut s: Vec<_> = targets.iter().map(|(_, b)| *b).collect();
                s.push(*otherwise);
                s.dedup();
                s
            }
            Self::Return | Self::Unreachable     => vec![],
            Self::Call { destination: Some((_, b)), .. } => vec![*b],
            Self::Call { destination: None, .. } => vec![],
            Self::DropAndGoto { target, .. }     => vec![*target],
        }
    }
}

// ── Basic Block ───────────────────────────────────────────────────────────────

/// A unique identifier for a basic block within a function's CFG
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BlockId(pub u32);

impl BlockId {
    /// The conventional entry block of a function
    pub const ENTRY: BlockId = BlockId(0);
}

impl std::fmt::Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BB{}", self.0)
    }
}

/// A basic block: A straight-line sequence of statements and a terminator
#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub id: BlockId,
    pub stmts: Vec<Statement>,
    pub terminator: Option<Terminator>, // None while still being built
}

