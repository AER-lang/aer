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
