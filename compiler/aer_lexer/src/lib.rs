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

    // ── Integer literals ──────────────────────────────────────────────────────

    #[test]
    fn decimal_int() {
        let k = kinds("0 1 42 999");
        assert_eq!(k, vec![
            TokenKind::IntLit(0),
            TokenKind::IntLit(1),
            TokenKind::IntLit(42),
            TokenKind::IntLit(999),
            TokenKind::Eof,
        ]);
    }

    #[test]
    fn hex_int() {
        let k = kinds("0xFF 0x0 0xDEAD_BEEF");
        assert_eq!(k, vec![
            TokenKind::IntLit(255),
            TokenKind::IntLit(0),
            TokenKind::IntLit(0xDEAD_BEEF),
            TokenKind::Eof,
        ]);
    }

    #[test]
    fn binary_int() {
        let k = kinds("0b1010 0b0 0b1111_0000");
        assert_eq!(k, vec![
            TokenKind::IntLit(0b1010),
            TokenKind::IntLit(0),
            TokenKind::IntLit(0b1111_0000),
            TokenKind::Eof,
        ]);
    }

    #[test]
    fn octal_int() {
        let k = kinds("0o777 0o0 0o644");
        assert_eq!(k, vec![
            TokenKind::IntLit(0o777),
            TokenKind::IntLit(0),
            TokenKind::IntLit(0o644),
            TokenKind::Eof,
        ]);
    }

    #[test]
    fn int_with_suffix() {
        // Suffix is consumed but doesn't change the kind
        let k = kinds("42i32 100u64 0usize");
        assert_eq!(k, vec![
            TokenKind::IntLit(42),
            TokenKind::IntLit(100),
            TokenKind::IntLit(0),
            TokenKind::Eof,
        ]);
    }

    #[test]
    fn int_underscore_separator() {
        let k = kinds("1_000_000");
        assert_eq!(k, vec![TokenKind::IntLit(1_000_000), TokenKind::Eof]);
    }

    // ── Float literals ────────────────────────────────────────────────────────

    #[test]
    fn basic_float() {
        let k = kinds("3.14 0.0 1.0");
        assert!(matches!(k[0], TokenKind::FloatLit(v) if (v - 3.14).abs() < 1e-10));
        assert!(matches!(k[1], TokenKind::FloatLit(v) if v == 0.0));
        assert!(matches!(k[2], TokenKind::FloatLit(v) if v == 1.0));
    }

    #[test]
    fn float_with_exponent() {
        let k = kinds("1e10 2.5e-3 1E+6");
        assert!(matches!(k[0], TokenKind::FloatLit(v) if (v - 1e10).abs() < 1.0));
        assert!(matches!(k[1], TokenKind::FloatLit(v) if (v - 2.5e-3).abs() < 1e-10));
        assert!(matches!(k[2], TokenKind::FloatLit(v) if (v - 1e6).abs() < 1.0));
    }

    // ── String literals ───────────────────────────────────────────────────────

    #[test]
    fn simple_string() {
        let k = kinds(r#""hello""#);
        assert_eq!(k, vec![TokenKind::StringLit("hello".into()), TokenKind::Eof]);
    }

    #[test]
    fn string_escapes() {
        let k = kinds(r#""\n\t\\\"""#);
        assert_eq!(k, vec![TokenKind::StringLit("\n\t\\\"".into()), TokenKind::Eof]);
    }

    #[test]
    fn string_unicode_escape() {
        let k = kinds(r#""\u{1F600}""#);
        assert_eq!(k, vec![TokenKind::StringLit("😀".into()), TokenKind::Eof]);
    }

    #[test]
    fn unterminated_string() {
        let (_tokens, errors) = lex(r#""oops"#);
        assert!(!errors.is_empty());
        assert!(errors[0].message.contains("unterminated string literal"));
    }
}
