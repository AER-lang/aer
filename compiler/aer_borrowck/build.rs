//! AST → CFG lowering for the ÆR borrow checker
//!
//! Walks a parsed function body and produces a Cfg with explicit
//! control-flow edges, place-based assignaments, and storage annotations
//!
//! Lowering Strategy
//!
//! We use a builder pattern: A CfgBuilder holds the CFG under construction
//! and a current block cursor. Lowering an expression appends statements
//! to the current block and possibly creates new blocks (for if/else,
//! loops, etc.) returning the place that holds the result.
//!
//! Expressions that produce values always write their result into a fresh
//! temporary local. This SSA-like discipline keeps the borrow checker
//! analysis simple: every definition site is a single Assign statement.

use aer_lexer::Span;
use aer_parser::ast::*;
use aer_tycheck::{TypeId, CheckResult};
use aer_tycheck::symbols::DefKind;

use crate::cfg::*;

// ── Builder ───────────────────────────────────────────────────────────────────

pub struct CfgBuilder<'tcx> {
    cfg:    Cfg,
    /// Thew block currently being filled
    current: BlockId,
    /// Type-check results, used to look up types of expressions
    tcx:    &'tcx CheckResult,
    /// Mapping from source-span starts to LocalIds, for resolving names
    locals: std::collections::HashMap<String, LocalId>,
    /// Temporary counter
    tmp:    u32,
}
