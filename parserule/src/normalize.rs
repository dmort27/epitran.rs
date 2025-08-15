//! Unicode normalization utilities for language data
//!
//! This module provides NFD (Normalized Form Decomposition) normalization
//! for all language data that enters the system from external sources.

use unicode_normalization::UnicodeNormalization;

/// Normalize text using NFD (Normalized Form Decomposition)
///
/// This function should be applied to all language data that comes from
/// external sources including:
/// - Map files (.csv)
/// - Preprocessor files (.txt) 
/// - Postprocessor files (.txt)
/// - Test files
/// - User input
/// - Any hardcoded language data
///
/// # Arguments
/// * `text` - The input text to normalize
///
/// # Returns
/// The NFD-normalized text as a String
pub fn nfd_normalize(text: &str) -> String {
    text.nfd().collect()
}

/// Normalize each line in a multi-line text using NFD
///
/// This is a convenience function for normalizing files that contain
/// multiple lines of language data.
///
/// # Arguments
/// * `text` - The multi-line input text to normalize
///
/// # Returns
/// The text with each line NFD-normalized
pub fn nfd_normalize_lines(text: &str) -> String {
    text.lines()
        .map(|line| nfd_normalize(line))
        .collect::<Vec<_>>()
        .join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nfd_normalize_basic() {
        // Test basic ASCII text (should remain unchanged)
        assert_eq!(nfd_normalize("hello"), "hello");
        assert_eq!(nfd_normalize("test123"), "test123");
    }

    #[test]
    fn test_nfd_normalize_composed_characters() {
        // Test composed characters that should be decomposed
        let cafe_composed = "café"; // é is a single composed character
        let cafe_normalized = nfd_normalize(cafe_composed);
        
        // The é should be decomposed into e + combining acute accent
        assert!(cafe_normalized.len() > cafe_composed.len());
        assert!(cafe_normalized.contains('e'));
        
        // Test with other composed characters
        let naive_composed = "naïve"; // ï is a single composed character
        let naive_normalized = nfd_normalize(naive_composed);
        assert!(naive_normalized.len() > naive_composed.len());
    }

    #[test]
    fn test_nfd_normalize_already_decomposed() {
        // Test text that's already in NFD form
        let already_nfd = "cafe\u{0301}"; // e + combining acute accent
        let normalized = nfd_normalize(already_nfd);
        assert_eq!(normalized, already_nfd); // Should remain the same
    }

    #[test]
    fn test_nfd_normalize_mixed_scripts() {
        // Test with mixed scripts
        assert_eq!(nfd_normalize("hello世界"), "hello世界");
        assert_eq!(nfd_normalize("Привет"), "Привет");
        assert_eq!(nfd_normalize("こんにちは"), "こんにちは");
    }

    #[test]
    fn test_nfd_normalize_lines() {
        let input = "café\nnaïve\nhello";
        let normalized = nfd_normalize_lines(input);
        
        // Each line should be normalized
        let lines: Vec<&str> = normalized.lines().collect();
        assert_eq!(lines.len(), 3);
        
        // First line should be longer due to decomposition
        assert!(lines[0].len() > 4); // "café" becomes longer
        assert!(lines[1].len() > 5); // "naïve" becomes longer  
        assert_eq!(lines[2], "hello"); // ASCII remains the same
    }

    #[test]
    fn test_nfd_normalize_empty_and_whitespace() {
        assert_eq!(nfd_normalize(""), "");
        assert_eq!(nfd_normalize(" "), " ");
        assert_eq!(nfd_normalize("\t\n"), "\t\n");
    }
}