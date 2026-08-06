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

    // ── Whitespace & comments ─────────────────────────────────────────────────

    #[test]
    fn empty_input() {
        let (tokens, errors) = lex("");
        assert!(errors.is_empty());
        assert_eq!(tokens.len(), 1);
        assert!(tokens[0].is_eof());
    }

    #[test]
    fn only_whitespace() {
        let k = kinds("   \t\n  ");
        assert_eq!(k, vec![TokenKind::Eof]);
    }

    #[test]
    fn line_comment_skipped() {
        let k = kinds("// this is a comment\n42");
        assert_eq!(k, vec![TokenKind::IntLit(42), TokenKind::Eof]);
    }

    #[test]
    fn block_comment_skipped() {
        let k = kinds("/* hello */ 99");
        assert_eq!(k, vec![TokenKind::IntLit(99), TokenKind::Eof]);
    }

    #[test]
    fn block_comment_multiline() {
        let k = kinds("/* line1\n   line2\n */ true");
        assert_eq!(k, vec![TokenKind::KwTrue, TokenKind::Eof]);
    }

    #[test]
    fn unterminated_block_comment() {
        let (_tokens, errors) = lex("/* oops");
        assert!(!errors.is_empty());
        assert!(errors[0].message.contains("unterminated block comment"));
    }
}
