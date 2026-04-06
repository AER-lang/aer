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
}