//! aer_lexer - the ÆR language tokenizer
//!
//! Quick start
//!
//! use aer_lexer::{Lexer, TokenKind};
//!
//! let src = r#"fn add(a: i32, b: i32) -> i32 { a + b }"#;
//! let (tokens, errors) = Lexer::new(src).tokenize();
//! assert!(errors.is_empty());
//! assert!(matches!(tokens[0].kind, TokenKind::KwFn));

pub mod error;
pub mod lexer;
pub mod token;

pub use error::LexError;
pub use lexer::Lexer;
pub use token::{Span, Token, TokenKind};

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(src: &str) -> (Vec<Token>, Vec<LexError>) {
        lexer::new(src).tokenize()
    }

    fn kinds(src: &str) -> Vec<TokenKind> {
        let (tokens, errors) = lex(src);
        assert!(errors.is_empty(), "unexpected lex errors: {:?}", errors);
        tokens.into_iter().map(|t| t.kind).collect()
    }
}
