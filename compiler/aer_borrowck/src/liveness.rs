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

// ── Liveness result ───────────────────────────────────────────────────────────

/// The liveness information for a single function
pub struct LivenessResult {
    /// live_in[block] ➔ The set of locals live on entry to each block
    pub live_in: Vec<LiveSet>,
    /// live_out[block] ➔ The set of locals live on exit from each block
    pub live_out: Vec<LiveSet>,
}

impl LivenessResult {
    /// Is local live just before statement stmt_idx of block?
    ///
    /// We recompute this on demand from live_out by scanning the block backwards
    /// For the borrow checker's needs this is fast enough
    pub fn is_live_before(&self, cfg: &Cfg, block: BlockId, stmt_idx: usize, local: LocalId) -> bool {
        // Start from live_out, then kill/gen backwards through the block stmts
        let mut live = self.live_out[block.0 as usize].clone();
        let bb = cfg.block(block);

        // Process terminator (if any) for uses
        if let Some(term) = &bb.terminator {
            collect_term_uses(&term.kind, &mut live);
        }

        // Walk statements in reverse until we hit stmt_idx
        for i in (stmt_idx..bb.stmts.len()).rev() {
            let stmt = &bb.stmts[i];
            // Kill any definition.
            if let Some(def_local) = stmt_def(stmt) {
                live.remove(def_local);
            }
            // Gen any uses
            stmt_uses(stmt, &mut live);
            if i == stmt_idx {
                return live.contains(local);
            }
        }
        live.contains(local)
    }
}

// ── Main analysis ─────────────────────────────────────────────────────────────

/// Run backward liveness analysis over the CFG
pub fn analyse(cfg: &Cfg) -> LivenessResult {
    let n = cfg.blocks.len();
    let preds = cfg.predecessors();

    let mut live_in:  Vec<LiveSet> = vec![LiveSet::new(); n];
    let mut live_out: Vec<LiveSet> = vec![LiveSet::new(); n];

    // Iterate to fixed point
    let mut changed = true;
    while changed {
        changed = false;

        // Process blocks in reverse order (approximately reverse-post order)
        for i in (0..n).rev() {
            let bb = &cfg.blocks[i];
            let bid = bb.id;

            // live_out[B] = ⋃ live_in[S] for successors S
            if let Some(term) = &bb.terminator {
                for succ in term.kind.successors() {
                    let succ_in = live_in[succ.0 as usize].clone();
                    if live_out[i].union_with(&succ_in) {
                        changed = true;
                    }
                }
            }

            // Compute new live_in[B] by scanning this block backwards
            let mut live = live_out[i].clone();

            // Terminator uses
            if let Some(term) = &bb.terminator {
                collect_term_uses(&term.kind, &mut live);
            }

            // Statements in reverse
            for stmt in bb.stmts.iter().rev() {
                // Kill the defined local
                if let Some(def_local) = stmt_def(stmt) {
                    live.remove(def_local);
                }
                // Gen uses
                stmt_uses(stmt, &mut live);
            }

            // Parameter uses: params are always considered "used" at entry
            // (They are live from function start)
            for local in &cfg.locals {
                if local.is_param {
                    live.insert(local.id);
                }
            }

            if live != live_in[i] {
                live_in[i] = live;
                changed = true;
            }
        }
    }

    LivenessResult { live_in, live_out }
}
