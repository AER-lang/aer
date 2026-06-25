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

/// Parse args into an [Invocation], or an error message describing why
/// the arguments were invalid.
fn parse_args(args: &[String]) -> Result<Invocation, String> {
    let Some(command_name) = args.get(1) else {
        return Err(usage());
    };
    let Some(path) = args.get(2) else {
        return Err(usage());
    };
    let Some(command) = Command::parse(command_name) else {
        return Err(format!(
            "error: unknown subcommand '{command_name}'.\n{}",
            usage()
        ));
    };

    Ok(Invocation { command, path: path.clone() })
}

// ── Entry point ───────────────────────────────────────────────────────────────

/// Run the ÆR compiler driver
///
/// args matches std::env::args(): index 0 is the program name, index 1
/// the subcommand, index 2 the source file path. Returns the process exit
/// code, the caller is responsible for passing it to
/// std::process::exit/returning it from main
pub fn run(args: &[String]) -> ExitCode {
    report(try_run(args))
}

/// The testable core of [run]: parses arguments, reads the source file,
/// and dispatches to the requested subcommand
///
/// Kept separate from [run] so tests can inspect the Result directly
/// without depending on ExitCode equality (not available on all
/// supported toolchains)
fn try_run(args: &[String]) -> Result<(), Vec<String>> {
    let invocation = parse_args(args).map_err(|message| vec![message])?;

    let src = std::fs::read_to_string(&invocation.path).map_err(|e| {
        vec![format!("error: could not read '{}': {e}", invocation.path)]
    })?;

    match invocation.command {
        Command::Lex => cmd_lex(&src),
        Command::Parse => cmd_parse(&src),
        Command::Check => cmd_check(&src),
        Command::Borrow => cmd_borrow(&src),
        Command::EmitIr => cmd_emit_ir(&src),
        Command::Compile => cmd_compile(&invocation.path, &src),
    }
}

/// Translate a subcommand result into an exit code, printing any errors
///
/// This is the single place where compiler diagnostics are written to
/// stderr, every cmd_* function returns its errors as data rather than
/// printing them directly
fn report(result: Result<(), Vec<String>>) -> ExitCode {
    let Err(errors) = result else {
        return ExitCode::SUCCESS;
    };

    for error in &errors {
        eprintln!("{error}");
    }
    eprintln!("\n{} error(s).", errors.len());
    ExitCode::FAILURE
}

// ── Subcommands ───────────────────────────────────────────────────────────────

/// aer lex <file.ae> - Tokenize and print the token stream
fn cmd_lex(src: &str) -> Result<(), Vec<String>> {
    let (tokens, errors) = Lexer::new(src).tokenize();

    println!("{:<10} {:<22} {}", "SPAN", "KIND", "TEXT");
    println!("{}", "-".repeat(64));
    for tok in &tokens {
        if matches!(tok.kind, TokenKind::Eof) {
            println!("{:<10} {:<22}", tok.span, "<eof>");
            break;
        }
        let text = tok.span.slice(src);
        println!("{:<10} {:<22} {:?}", tok.span, tok.kind.description(), text);
    }

    if errors.is_empty() {
        return Ok(());
    }
    Err(errors.iter().map(|e| e.to_string()).collect())
}
