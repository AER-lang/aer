//! ÆR NLL Borrow checker
//!
//! # Overview
//!
//! After liveness analysis we know exactly where each variable is live.
//! The borrow checker uses that information to enforce three rules:
//!
//! 1. No use after move - Once a non-Copy value is moved out of a place,
//!     that place is uninitialized and cannot be read until re-assigned.
//!
//! 2. Borrow conflict - At any program point, a place may have either:
//!     - Any number of active shared borrows (&T), OR
//!     - Exactly one exclusive borrow (&mut T),
//!     but never both simultaneously, and the exclusive borrow is singular.
//!
//! 3. Mutability - Only places rooted at mut locals can be assigned to
//!     or borrowed as &mut.
//!
//! # NLL loan liveness
//!
//! A loan is created at each &place or &mut place rvalue. Under NLL,
//! the loan is live from its creation point to the last use of the reference
//! that was created from it. We approximate this with the liveness of the
//! reference variable itself: The loan is live as long as the local holding
//! the reference is live (per the liveness analysis).
//!
//! This is a sound (conservative) approximation for MVP purposes.

use std::collections::HashMap;

use aer_lexer::Span;

use crate::cfg::{
    BasicBlock, BlockId, Cfg, LocalId, Operand, Place, Rvalue, Statement,
    StatementKind, TerminatorKind,
};
use crate::error::{BorrowError, BorrowErrorKind, BorrowKind};
use crate::liveness::{LivenessResult, LiveSet};

// ── Loan ─────────────────────────────────────────────────────────────────────

/// A unique ID for a single borrow (loan) in the function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LoanId(pub u32);

/// A borrow of a place, create by a &place or &mut place rvalue.
#[derive(Debug, Clone)]
pub struct Loan {
    pub id:         LoanId,
    /// The place being borrowed.
    pub place:      Place,
    pub kind:       BorrowKind,
    /// The local that holds the resulting reference (so we can track liveness).
    pub ref_local:  LocalId,
    /// Source location of the borrow expression.
    pub span:       Span,
}

// ── Move state ────────────────────────────────────────────────────────────────

/// Tracks which locals have been moved-out-of and not yet re-initialized.
#[derive(Debug, Clone, Default)]
struct MoveState {
    moved: std::collections::HashSet<LocalId>,
}

impl MoveState {
    fn mark_moved(&mut self, id: LocalId) {
        self.moved.insert(id);
    }

    fn mark_initialized(&mut self, id: LocalId) {
        self.moved.remove(&id);
    }

    fn is_moved(&self, id: LocalId) -> bool {
        self.moved.contains(&id)
    }

    fn merge(&self, other: &MoveState) -> MoveState {
        // Conservative: A place is moved if it's moved on any incoming path.
        let moved = self.moved.union(&other.moved).copied().collect();
        MoveState { moved }
    }

// ── Borrow checker ────────────────────────────────────────────────────────────

pub struct BorrowChecker<'a> {
    cfg:        &'a Cfg,
    liveness:   &'a LivenessResult,
    /// All loans created in this function
    loans:      Vec<Loan>,
    errors:      Vec<BorrowError>,
}

impl<'a> BorrowChecker<'a> {
    pub fn new(cfg: &'a Cfg, liveness: &'a LivenessResult) -> Self {
        Self {
            cfg,
            liveness,
            loans: Vec::new(),
            errors: Vec::mew(),
        }
    }

    // ── Entry point ───────────────────────────────────────────────────────────

    /// Run the full borrow check pass and return any errors found.
    pub fn check(mut self) -> Vec<BorrowError> {
        // First pass: collect all loans (created by Ref / RefMut rvalues).
        self.collect_loans();

        // Second pass: check each block for violations.
        let mut move_state_at_entry: Vec<Option<MoveState>> =
            vec![None; self.cfg.blocks.len()];
        move_state_at_entry[BlockId::ENTRY.0 as usize] = Some(MoveState::default());

        // Process in a simple topological order (entry first, then BFS)
        let mut worklist: Vec<BlockId> = vec![BlockId::ENTRY];
        let mut visited: std::collections::HashSet<BlockId> = std::collections::HashSet::new();

        while let Some(bid) = worklist.pop() {
            if visited.contains(&bid) {
                continue;
            }
            visited.insert(bid);

            let entry_state = match move_state_at_entry[bid.0 as usize].clone() {
                Some(s) => s,
                None => MoveState::default(), // Uninitialized predecessor
            };

            let exit_state = self.check_block(bid, entry_state);

            // Propagate to successors.
            if let Some(term) = &self.cfg.block(bid).terminator {
                for succ in term.kind.successors() {
                    let merged = match &move_state_at_entry[succ.0 as usize] {
                        Some(existing) => existing merge(&exit_state),
                        None => exit_state.clone(),
                    };
                    move_state_at_entry[succ.0 as usize] = Some(merged);
                    worklist.push(succ);
                }
            }
        }

        self.errors
    }

    // ── Loan collection ───────────────────────────────────────────────────────

    fn collect_loans(&mut self) {
        for block in &self.cfg.blocks {
            for stmt in &block.stmts {
                if let StatementKind::Assign(lhs, rvalue) = &stmt.kind {
                    let ref_local = lhs.root;
                    match rvalue {
                        RValue:Ref(place) => {
                            let id = LoanId(self.loans.len() as u32);
                            self.loans.push(Loan {
                                id,
                                place: place.clone(),
                                kind: BorrowKind::Shared,
                                ref_local,
                                span: stmt.span,
                            });
                        }
                        Rvalue::RefMut(place) => {
                            let id = LoanId(self.loans.len() as u32);
                            self.loans.push(Loan {
                                id,
                                place: place.clone(),
                                kind: BorrowKind::Exclusive,
                                ref_local,
                                span: stmt.span,
                            });
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    // ── Active loans at a program point ──────────────────────────────────────

    /// Loans that are active (their reference variable is live) just before
    /// statement stmt_idx of block bid
    fn active_loans_before(&self, bid: BlockId, stmt_idx: usize) -> Vec<&Loan> {
        self.loans.iter().filter(|loan| {
            self.liveness.is_live_before(self.cfg, bid, stmt_idx, loan.ref_local)
        }).collect()
    }

    // ── Block checking ────────────────────────────────────────────────────────

    fn check_block(&mut self, bid: BlockId, mut state: MoveState) -> MoveState {
        let bb = self.cfg.block(bid);

        for (stmt_idx, stmt) in bb.stmts.iter().enumerate() {
            let active = self.active_loans_before(bid, stmt_idx);
            self.check_stmt(stmt, &active, &mut state);
        }

        // Check terminator
        if let Some(term) = &bb.terminator {
            let active = self.active_loans_before(bid, bb.stmts.len());
            self.check_terminator(term, &active, &mut state);
        }

        state
    }

    // ── Statement checking ────────────────────────────────────────────────────

    fn check_stmt(
        &mut self,
        stmt: &Statement,
        active: &[&Loan],
        state: &mut MoveState,
    ) {
        match &stmt.kind {
            StatementKind::Assign(lhs, rvalue) => {
                // Check the rvalue for moves / uses of moved values
                self.check_rvalue(rvalue, active, state, stmt.span);

                // Check that the lhs is mutable (if it's a direct local)
                if lhs.is_local() {
                    self.check_place_mutability(lhs, stmt.span);
                }

                // Check that no active loan covers the lhs place.
                for loan in active {
                    if self.places_conflict(&loan.place, lhs) {
                        self.errors.push(BorrowError::new(
                            stmt.span,
                            BorrowErrorKind::ConflictingBorrow {
                                place: lhs.to_string(),
                                existing_kind: loan.kind,
                                existing_span: loan.span,
                                new_kind: BorrowKind::Exclusive,
                            },
                        ));
                    }
                }

                // The lhs is now (re-)initialized
                if lhs.is_local() {
                    state.mark_initialized(lhs.root);
                }
            }

            StatementKind::Drop(place) => {
                // Check no active loan covers the dropped place.
                for loan in active {
                    if self.places_conflict(&loan.place, place) {
                        self.errors.push(BorrowError::new(
                            stmt.span,
                            BorrowErrorKind::MoveWhileBorrowed {
                                name: place.to_string(),
                                borrow_span: loan.span,
                            },
                        ));
                    }
                }
                if place.is_local() {
                    state.mark_moved(place.root);
                }
            }

            StatementKind::StorageDead(id) => {
                state.mark_moved(*id);
            }

            StatementKind::StorageLive(_) | StatementKind::Nop => {}
        }
    }

    // ── Rvalue checking ───────────────────────────────────────────────────────

    fn check_rvalue(
            &mut self,
            rv: &Rvalue,
            active: &[&Loan],
            state: &mut MoveState,
            span: Span,
        ) {
            match rv {
                Rvalue::Use(op) => {
                    self.check_operand_move(op, active, state, span);
                }
                Rvalue::Ref(place) => {
                    // Shared borrow - check no exclusive loan is active on a conflicting place.
                    self.check_use_of_place(place, state, span);
                    for loan in active {
                        if loan.kind == BorrowKind::Exclusive && self.places_conflict(place, &loan, place) {
                            self.errors.push(BorrowError::new(
                                span,
                                BorrowErrorKind::ConflictingBorrow {
                                    place: place.to_string(),
                                    existing_kind: loan.kind,
                                    existing_span: loan.span,
                                    new_kind: BorrowKind::Shared,
                                },
                            ));
                        }
                    }
                }
                RValue::RefMut(place) => {
                    // Exclusive borrow - check the place is mutable and no other loan is active.
                    self.check_place_mutability(place, span);
                    self.check_use_of_place(place, state, span);
                    for loan in active {
                        if self.places_conflict(place, &loan.place) {
                            self.errors.push(BorrowError::new(
                                span,
                                BorrowErrorKind::ConflictingBorrow {
                                    place: place.to_string(),
                                    existing_kind: loan.kind,
                                    existing_span: loan.span,
                                    new_kind: BorrowKind::Exclusive,
                                },
                            ));
                        }
                    }
                }
                Rvalue::BinaryOp(_, a, b) => {
                    self.check_operand_move(a, active, state, span);
                    self.check_operand_move(b, active, state, span);
                }
                Rvalue::UnaryOp(_, a) => {
                    self.check_operand_move(op, active, state, span);
                }
                Rvalue::Aggregate(_, ops) => {
                    for op in ops {
                        self.check_operand_move(op, active, state, span);
                    }
                }
            }
        }

        fn check_operand_move(
            &mut self,
            op: &Operand,
            active: &[&Loan],
            state: &mut MoveState,
            span: span
        ) {
            match op {
                Operand::Move(place) => {
                    // Check not moved already
                    self.check_use_of_place(place, state, span);

                    // Check no active loan is on a conflicting place
                    for loan in active {
                        if self.places_conflict(place, &loan.place) {
                            self.errors.push(BorrowError::new(
                                span,
                                BorrowErrorKind::MoveWhileBorrowed {
                                    name: place.to_string(),
                                    borrow_span: loan.span,
                                },
                            ));
                        }
                    }

                    // Mark as moved (for non-Copy types)
                    // As this is currently a MVP we are treating all non-primitive locals as moved
                    // on use
                    // A Copy analysis pass would refine this
                    if place.is_local() {
                        let local = self.cfg.local(place.root);
                        if !is_copy_type(local.ty) {
                            state.mark_moved(place.root);
                        }
                    }
                }
                Operand::Const(_) => {}
            }
        }

        fn check_use_of_place(&mut self, place: &Place, state: &MoveState, span: Span) {
            if place.is_local() && state.is_moved(place.root) {
                let name = self.cfg.local(place.root).name.clone();
                // Only emit if the span is meaningful (not a compiler-generated tmp)
                if !name.starts_with("_t") {
                    self.errors.push(BorrowError::new(
                        span,
                        BorrowErrorKind::UseAfterMove {
                            name,
                            move_at: span, // Ideally the original move span
                        },
                    ));
                }
            }
        }

    // ── Terminator checking ───────────────────────────────────────────────────

    fn check_terminator(
            &mut self,
            term: &crate::cfg::Terminator,
            active: &[&Loan],
            state: &mut MoveState,
        ) {
            match &term.kind {
                TerminatorKind::Return => {
                    let ret = Place::local(LocalId::RETURN);
                    self.check_use_of_place(&ret, state, term.span);
                }
                TerminatorKind::Call { func, args, .. } => {
                    self.check_operand_move(func, active, state, term.span);
                    for arg in args {
                        self.check_operand_move(arg, active, state, term.span);
                    }
                }
                TerminatorKind::SwitchInt { discriminant, .. } => {
                    self.check_operand_move(discriminant, active, state, term.span);
                }
                TerminatorKind::DropAndGoto { place, .. } => {
                    for loan in active {
                        if self.places_conflict(place, &loan.place) {
                            self.errors.push(BorrowError::new(
                                term.span,
                                BorrowErrorKind::MoveWhileBorrowed {
                                    name: place.to_string(),
                                    borrow_span: loan.span,
                                },
                            ));
                        }
                    }
                    if place.is_local() {
                        state.mark_moved(place.root);
                    }
                }
                TerminatorKind::Goto(_) | TerminatorKind::Unreachable => {}
            }
        }

    // ── Mutability checking ───────────────────────────────────────────────────

    fn check_place_mutability(&mut self, place: &Place, span: Span) {
            let local = self.cfg.local(place.root);
            if !local.mutable && !local.is_param {
                // Params are not mutable by default but that's a distinct error.
                // Only emit for explicit immutable lets
                if !local.name.starts_with("_t") {
                    self.errors.push(BorrowError::new(
                        span,
                        if matches!(place.proj.last(), None) {
                            BorrowErrorKind::MutationOfImmutable { name: local.name.clone() }
                        } else {
                            BorrowErrorKind::RefMutOfImmutable { name: local.name.clone() }
                        },
                    ));
                }
            }
        }

    // ── Place conflict ────────────────────────────────────────────────────────

    /// Two places conflict if one is a prefix of the other (i.e. they
    /// potentially alias the same memory)
    fn places_conflict(&self, a: &Place, b: &Place) -> bool {
            a.has_prefix(b) || b.has_prefix(a)
        }
}

// ── Copy type heuristic ───────────────────────────────────────────────────────

/// Returns true for types that implement Copy - They don't need to be
/// tracked for moves. In this MVP stage we use a conservative approximation:
/// all primitive types are Copy
fn is_copy_type(ty: aer_tycheck::TypeId) -> bool {
        ty.is_integer() || ty.is_float() || ty == aer_tycheck::TypeId::BOOL
}
