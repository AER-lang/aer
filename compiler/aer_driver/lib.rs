//! aer_driver - ÆR compiler pipeline orchestration.
//!
//! This crate owns the command-line interface and wires
//! together every compiler stage (aer_lexer through aer_codegen_llvm)
//! behind a small set of subcommands. The binary itself,
//! compiler/aer, is a three-line shim that calls [run]
//! all logic lives here so it can be exercised directly from tests without
//! spawning a process.
//!
//! Subcommands
//!
//! +-----------------------------------------------------------------+
//! | Subcommand | Pipeline stage exercised | Output                  |
//! +------------|--------------------------|-------------------------+
//! | lex        | aer_lexer                | Token stream            |
//! | parse      | aer_parse                | AST Summary             |
//! | check      | aer_hir_analysis         | Type error, if any      |
//! | borrow     | aer_borrowck             | Borrow errors, if any   |
//! | emit-ir    | aer_codegen_llvm         | LLVM IR text            |
//! | compile    | aer_codegen_llvm         | Native object file (.o) |
//! +-----------------------------------------------------------------+
//!
//! Design
//!
//! [run] takes args (matching std::env::args(), including the program
//! name at index 0) and returns an [ExitCode]. It never calls
//! std::process::exit itself, that decision belongs to the binary crate.
//! Each cmd_* function does one thing and returns
//! Result<(), Vec<String>>; [run] is the single place that turns errors
//! into diagnostic output, so error formatting isn't duplicated six times.

use std::process::ExitCode;

use aer_ast::ItemKind;
use aer_borrowck::check_source as borrow_check_source;
use aer_codegen_llvm::{compile_to_ir, compile_to_object};
use aer_hir_analysis::check_source;
use aer_lexer::{Lexer, TokenKind};
use aer_parse::parse_source;
use inkwell::OptimizationLevel;

// ── CLI argument parsing ──────────────────────────────────────────────────────

/// A successfully parsed command-line invocation
struct Invocation {
    command: Command,
    path: String,
}

/// The subcommand requested on the command line
enum Command {
    Lex,
    Parse,
    Check,
    Borrow,
    EmitIr,
    Compile,
}

impl Command {
    /// Parse a subcommand name, or None if it isn't recognized
    fn parse(name: &str) -> Option<Command> {
        match name {
            "lex" => Some(Command::Lex),
            "parse" => Some(Command::Parse),
            "check" => Some(Command::Check),
            "borrow" => Some(Command::Borrow),
            "emit-ir" => Some(Command::EmitIr),
            "compile" => Some(Command::Compile),
            _ => None,
        }
    }
}

/// The one-line usage string. Shared between the "missing arguments" and
/// "unknown subcommand" error paths so the two can never drift apart
fn usage() -> String {
    "Usage: aer <lex|parse|check|borrow|emit-ir|compile> <file.ae>".to_string()
}
