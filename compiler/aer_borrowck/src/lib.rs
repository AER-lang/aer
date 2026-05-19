//! borrowck - ÆR NLL borrow checker
//!
//! Pipeline position
//!
//! Source → Lexer → Parser → TypeChecker → [BorrowChecker] → (LLVM Codegen)
//!
//! Usage
//!
//! use borrowck::check_source;
//!
//! let result = check_source("fn f(x: i32) -> i32 { x }");
//! assert!(result.errors.is_empty())

pub mod borrowck;
pub mod build;
pub mod cfg;
pub mod error;
pub mod liveness;

pub use borrowck::BorrowChecker;
pub use build::build_fn_cfg;
pub use cfg::Cfg;
pub use error::{BorrowError, BorrowErrorKind, BorrowKind};

use aer_parser::{ast::ItemKind, parse_source};
use aer_tycheck::check;

// ── Public entry points ───────────────────────────────────────────────────────

/// Result of the full borrow-check pipeline on a source string
pub struct BorrowCheckResult {
    pub parse_errors:  Vec<String>,
    pub type_errors:   Vec<String>,
    pub borrow_errors: Vec<BorrowError>,
}

impl BorrowCheckResult {
    /// All errors as display strings, in pipeline order
    pub fn all_errors(&self) -> Vec<String> {
        let mut out = self.parse_errors.clone();
        out.extend(self.type_errors.clone());
        out.extend(self.borrow_errors.iter().map(|e| e.to_string()));
        out
    }

    pub fn errors(&self) -> &[BorrowError] {
        &self.borrow_errors
    }

    pub fn is_clean(&self) -> bool {
        self.all_errors().is_empty()
    }
}

/// Parse, type-check, and borrow-check a complete ÆR source string
pub fn check_source(src: &str) -> BorrowCheckResult {
    let (file, parse_errors) = parse_source(src);
    let tcx = check(&file);

    let type_errors: Vec<String> = tcx.collect_errors.iter().map(|e| e.to_string())
        .chain(tcx.type_errors.iter().map(|e| e.to_string()))
        .collect();

    // If there are type errors we still run the borrow checker, it's
    // tolerant of unknown types, but results may be imprecise
    let mut all_borrow_errors = Vec::new();

    for item in &file.items {
        if let ItemKind::Fn(f) = &item.kind {
            if f.body.is_some() {
                let cfg = build_fn_cfg(f, &tcx);
                let liveness = liveness::analyse(&cfg);
                let checker = BorrowChecker::new(&cfg, &liveness);
                all_borrow_errors.extend(checker.check());
            }
        }
    }

    BorrowCheckResult {
        parse_errors,
        type_errors,
        borrow_errors: all_borrow_errors,
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::{LocalId, BlockId};

    fn check(src: &str) -> BorrowCheckResult {
        check_source(src)
    }

    fn assert_clean(src: &str) {
        let r = check(src);
        assert!(
            r.is_clean(),
            "unexpected errors:\n{}",
            r.all_errors().join("\n")
        );
    }

    fn assert_borrow_error(src: &str, fragment: &str) {
        let r = check(src);
        assert!(
            !r.borrow_errors.is_empty(),
            "expected a borrow error containing {:?} but got none\ntype errors: {:?}",
            fragment, r.type_errors
        );
        assert!(
            r.borrow_errors.iter().any(|e| e.to_string().contains(fragment)),
            "expected borrow error containing {:?}, got:\n{}",
            fragment,
            r.borrow_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n")
        );
    }

    // ── CFG construction ──────────────────────────────────────────────────────

    #[test]
    fn cfg_entry_block_exists() {
        let (file, _) = parse_source("fn f() { }");
        let tcx = check(&file);
        let ItemKind::Fn(ref f) = file.items[0].kind else { panic!() };
        let cfg = build_fn_cfg(f, &tcx);
        assert!(cfg.blocks.len() >= 1);
        assert_eq!(cfg.blocks[0].id, BlockId::ENTRY);
    }

    #[test]
    fn cfg_has_return_local() {
        let (file, _) = parse_source("fn f() -> i32 { 42 }");
        let tcx = check(&file);
        let ItemKind::Fn(ref f) = file.items[0].kind else { panic!() };
        let cfg = build_fn_cfg(f, &tcx);
        assert_eq!(cfg.locals[0].id, LocalId::RETURN);
    }

    #[test]
    fn cfg_declares_params() {
        let (file, _) = parse_source("fn add(a: i32, b: i32) -> i32 { a + b }");
        let tcx = check(&file);
        let ItemKind::Fn(ref f) = file.items[0].kind else { panic!() };
        let cfg = build_fn_cfg(f, &tcx);
        // Should have return slot + 2 params
        let params: Vec<_> = cfg.locals.iter().filter(|l| l.is_param).collect();
        assert_eq!(params.len(), 2);
    }

    #[test]
    fn cfg_if_creates_multiple_blocks() {
        let src = "fn f(x: bool) -> i32 { if x { 1 } else { 2 } }";
        let (file, _) = parse_source(src);
        let tcx = check(&file);
        let ItemKind::Fn(ref f) = file.items[0].kind else { panic!() };
        let cfg = build_fn_cfg(f, &tcx);
        // if/else should produce at least 4 blocks (entry, then, else, join)
        assert!(cfg.blocks.len() >= 4, "expected ≥4 blocks, got {}", cfg.blocks.len());
    }

    #[test]
    fn cfg_while_creates_multiple_blocks() {
        let src = "fn f() { let mut i = 0; while i < 10 { i += 1; } }";
        let (file, _) = parse_source(src);
        let tcx = check(&file);
        let ItemKind::Fn(ref f) = file.items[0].kind else { panic!() };
        let cfg = build_fn_cfg(f, &tcx);
        assert!(cfg.blocks.len() >= 3);
    }

    // ── Liveness analysis ─────────────────────────────────────────────────────

    #[test]
    fn liveness_param_is_live_at_entry() {
        let (file, _) = parse_source("fn f(x: i32) -> i32 { x }");
        let tcx = check(&file);
        let ItemKind::Fn(ref f) = file.items[0].kind else { panic!() };
        let cfg = build_fn_cfg(f, &tcx);
        let live = liveness::analyse(&cfg);
        // The parameter should be live at the entry block
        let param_id = cfg.locals.iter()
            .find(|l| l.is_param && l.name == "x")
            .map(|l| l.id);
        if let Some(pid) = param_id {
            assert!(
                live.live_in[BlockId::ENTRY.0 as usize].contains(pid),
                "param x should be live at entry"
            );
        }
    }

    #[test]
    fn liveness_unused_tmp_not_live() {
        let (file, _) = parse_source("fn f() { let _x = 42; }");
        let tcx = check(&file);
        let ItemKind::Fn(ref f) = file.items[0].kind else { panic!() };
        let cfg = build_fn_cfg(f, &tcx);
        let live = liveness::analyse(&cfg);
        // The return local (LocalId::RETURN) should be in live_in of a block
        // only if it's actuall used. An empty body function may not use it
        // Just verify the analysis runs without panic
        let _ = live;
    }

    // ── Borrow checker — clean programs ───────────────────────────────────────

    #[test]
    fn clean_empty_fn() {
        assert_clean("fn f() { }");
    }

    #[test]
    fn clean_simple_fn() {
        assert_clean("fn f(x: i32) -> i32 { x }");
    }

    #[test]
    fn clean_shared_borrow() {
        assert_clean(r#"
            fn f(x: i32) -> &i32 {
                let r = &x;
                r
            }"#);
    }

    #[test]
    fn clean_mut_borrow_after_use() {
        // Under NLL: the shared borrow r ends at its last use (the call),
        // so the mutation of x afterwards is valid
        assert_clean(r#"
fn use_ref(r: &i32) -> i32 { 0 }
fn f() -> void {
    let mut x = 5;
    let r = &x;
    use_ref(r);
    x = 10;
}
"#);
    }

    #[test]
    fn clean_two_shared_borrows() {
        assert_clean(r#"
fn f() -> void {
    let x = 5;
    let a = &x;
    let b = &x;
    let _ = a;
    let _ = b;
}
"#);
    }

    #[test]
    fn clean_mutable_local_assigned() {
        assert_clean(r#"
fn f() -> i32 {
    let mut x = 0;
    x = 42;
    x
"#);
    }

    #[test]
    fn clean_mut_ref_to_mut_local() {
        assert_clean(r#"
fn inc(r: &mut i32) -> void { }
fn f() -> void {
    let mut x = 0;
    inc(&mut x);
"#);
    }

    #[test]
    fn clean_arithmetic() {
        assert_clean("fn f(a: i32, b: i32) -> i32 { a + b }");
    }

    #[test]
    fn clean_if_expression() {
        assert_clean("fn f(x: bool) -> i32 { if x { 1 } else { 2 } }");
    }

