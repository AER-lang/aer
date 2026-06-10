//! Liveness analysis for the ÆR NLL borrow checker.
//!
//! What is liveness?
//!
//! A variable is live at a program point if there exists a path from that
//! point to a future use of the variable without an intervening kill
//! (re-assignment or StorageDead)
//!
//! Under NLL, a borrow is live only between its creation and its last use,
//! not until the end of its lexical scope. This is precisely what the liveness
//! analysis computes
//!
//! Algorithm
//!
//! Standard backward dataflow:
//!
//! live_out[B] = ⋃  live_in[S]   for each successor S of B
//! live_in[B]  = use[B] ∪ (live_out[B] − def[B])
//!
//! Output
//!
//! A LivenessResult maps each (BlockId, statement index) to the set of
//! LocalId s that are live before that statement

use std::collections::{HashMap, HashSet};

use crate::cfg::{BasicBlock, BlockId, Cfg, LocalId, Operand, Place, Rvalue, StatementKind, TerminatorKind};

// ── LiveSet ───────────────────────────────────────────────────────────────────

/// A set of live local variables, represented as a sorted Vec for fast
/// merging and diffing
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LiveSet(pub HashSet<LocalId>);

impl LiveSet {
    pub fn new() -> Self { Self(HashSet::new()) }

    pub fn insert(&mut self, id: LocalId) -> bool {
        self.0.insert(id)
    }

    pub fn remove(&mut self, id: LocalId) {
        self.0.remove(&id);
    }

    pub fn contains(&self, id: LocalId) -> bool {
        self.0.contains(&id)
    }

    /// Union in-place
    /// Returns true if the set changed
    pub fn union_with(&mut self, other: &LiveSet) -> bool {
        let before = self.0.len();
        for &id in &other.0 {
            self.0.insert(id);
        }
        self.0.len() != before
    }
}
