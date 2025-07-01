use unicode_segmentation::UnicodeSegmentation;
use std::collections::HashSet;

/// Tokenizes text by whitespace, returning sequences of graphemes without whitespace or punctuation.
/// 
/// This function splits the input text by whitespace and then filters out any tokens that contain
/// only punctuation characters, returning only sequences of letters, digits, and other non-punctuation
/// graphemes. Each token is wrapped with the specified boundary string.
/// 
/// # Arguments
/// 
/// * `text` - A string slice containing the text to tokenize
/// * `boundary` - A string slice to be added to the beginning and end of each token
/// 
/// # Returns
/// 
/// A vector of strings, where each string is a sequence of graphemes with no whitespace or punctuation,
/// wrapped with the specified boundary string
/// 
/// # Examples
/// 
/// ```
/// use rsepitran::tokenize::tokenize_by_whitespace;
/// 
/// let text = "Hello, world! This is a test.";
/// let tokens = tokenize_by_whitespace(text, "#");
/// assert_eq!(tokens, vec!["#Hello#", "#world#", "#This#", "#is#", "#a#", "#test#"]);
/// ```
pub fn tokenize_by_whitespace(text: &str, boundary: &str) -> Vec<String> {
    text.split_whitespace()
        .map(|word| {
            // Remove punctuation from the beginning and end of each word
            let graphemes: Vec<&str> = word.graphemes(true).collect();
            let mut start = 0;
            let mut end = graphemes.len();
            
            // Find the first non-punctuation character
            while start < graphemes.len() && is_punctuation(graphemes[start]) {
                start += 1;
            }
            
            // Find the last non-punctuation character
            while end > start && is_punctuation(graphemes[end - 1]) {
                end -= 1;
            }
            
            // Join the remaining graphemes and wrap with boundary
            let clean_token = graphemes[start..end].join("");
            if clean_token.is_empty() {
                clean_token
            } else {
                format!("{}{}{}", boundary, clean_token, boundary)
            }
        })
        .filter(|token| !token.is_empty()) // Remove empty tokens
        .collect()
}

/// Helper function to determine if a grapheme is punctuation
fn is_punctuation(grapheme: &str) -> bool {
    grapheme.chars().all(|c| {
        // Use ASCII punctuation check and a simple Unicode range check
        c.is_ascii_punctuation() || 
        // Check for common Unicode punctuation ranges
        (c as u32 >= 0x2000 && c as u32 <= 0x206F) || // General Punctuation
        (c as u32 >= 0x3000 && c as u32 <= 0x303F) || // CJK Symbols and Punctuation
        (c as u32 >= 0xFE30 && c as u32 <= 0xFE4F) || // CJK Compatibility Forms
        (c as u32 >= 0xFE50 && c as u32 <= 0xFE6F) || // Small Form Variants
        (c as u32 >= 0xFF00 && c as u32 <= 0xFFEF) || // Halfwidth and Fullwidth Forms
        // Common individual punctuation characters
        matches!(c, '¡' | '¿' | '§' | '¶' | '†' | '‡' | '•' | '…' | '‰' | '‱')
    })
}

/// Filters input string to only contain substrings that are elements of the provided symbol set.
/// 
/// This function performs a greedy longest-match filtering, where it tries to match the longest
/// possible substring from the symbol set at each position. If no match is found, that character
/// is skipped. The result is a concatenation of all matched symbols.
/// 
/// # Arguments
/// 
/// * `input` - A string slice containing the text to filter
/// * `syms` - A HashSet of strings representing the allowed symbols
/// 
/// # Returns
/// 
/// A string containing only the concatenated symbols from the set that were found in the input
/// 
/// # Examples
/// 
/// ```
/// use rsepitran::tokenize::filter_by_symbols;
/// use std::collections::HashSet;
/// 
/// let mut syms = HashSet::new();
/// syms.insert("hello".to_string());
/// syms.insert("world".to_string());
/// syms.insert("h".to_string());
/// syms.insert("e".to_string());
/// 
/// let input = "hello world!";
/// let result = filter_by_symbols(input, &syms);
/// assert_eq!(result, "helloworld");
/// ```
pub fn filter_by_symbols(input: &str, syms: &HashSet<String>) -> String {
    let mut result = String::new();
    let mut i = 0;
    let input_chars: Vec<char> = input.chars().collect();
    
    while i < input_chars.len() {
        let mut matched = false;
        let mut best_match_len = 0;
        let mut best_match = String::new();
        
        // Try to find the longest matching symbol starting at position i
        for j in (i + 1)..=input_chars.len() {
            let candidate: String = input_chars[i..j].iter().collect();
            if syms.contains(&candidate) {
                if candidate.len() > best_match_len {
                    best_match_len = candidate.len();
                    best_match = candidate;
                    matched = true;
                }
            }
        }
        
        if matched {
            result.push_str(&best_match);
            i += best_match.chars().count();
        } else {
            // No match found, skip this character
            i += 1;
        }
    }
    
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_tokenization() {
        let text = "Hello world";
        let tokens = tokenize_by_whitespace(text, "#");
        assert_eq!(tokens, vec!["#Hello#", "#world#"]);
    }

    #[test]
    fn test_punctuation_removal() {
        let text = "Hello, world! This is a test.";
        let tokens = tokenize_by_whitespace(text, "#");
        assert_eq!(tokens, vec!["#Hello#", "#world#", "#This#", "#is#", "#a#", "#test#"]);
    }

    #[test]
    fn test_multiple_punctuation() {
        let text = "Hello... world!!! Test???";
        let tokens = tokenize_by_whitespace(text, "#");
        assert_eq!(tokens, vec!["#Hello#", "#world#", "#Test#"]);
    }

    #[test]
    fn test_mixed_punctuation() {
        let text = "\"Hello,\" he said. 'World!' (test)";
        let tokens = tokenize_by_whitespace(text, "#");
        assert_eq!(tokens, vec!["#Hello#", "#he#", "#said#", "#World#", "#test#"]);
    }

    #[test]
    fn test_empty_and_whitespace() {
        let text = "   Hello    world   ";
        let tokens = tokenize_by_whitespace(text, "#");
        assert_eq!(tokens, vec!["#Hello#", "#world#"]);
    }

    #[test]
    fn test_only_punctuation() {
        let text = "!!! ... ??? ,,,";
        let tokens = tokenize_by_whitespace(text, "#");
        assert_eq!(tokens, Vec::<String>::new());
    }

    #[test]
    fn test_numbers_and_letters() {
        let text = "Hello123 world456!";
        let tokens = tokenize_by_whitespace(text, "#");
        assert_eq!(tokens, vec!["#Hello123#", "#world456#"]);
    }

    #[test]
    fn test_unicode_characters() {
        let text = "Héllo wörld café";
        let tokens = tokenize_by_whitespace(text, "#");
        assert_eq!(tokens, vec!["#Héllo#", "#wörld#", "#café#"]);
    }

    #[test]
    fn test_empty_string() {
        let text = "";
        let tokens = tokenize_by_whitespace(text, "#");
        assert_eq!(tokens, Vec::<String>::new());
    }

    #[test]
    fn test_different_boundaries() {
        let text = "Hello world";
        
        // Test with different boundary strings
        let tokens_hash = tokenize_by_whitespace(text, "#");
        assert_eq!(tokens_hash, vec!["#Hello#", "#world#"]);
        
        let tokens_pipe = tokenize_by_whitespace(text, "|");
        assert_eq!(tokens_pipe, vec!["|Hello|", "|world|"]);
        
        let tokens_bracket = tokenize_by_whitespace(text, "<>");
        assert_eq!(tokens_bracket, vec!["<>Hello<>", "<>world<>"]);
        
        let tokens_empty = tokenize_by_whitespace(text, "");
        assert_eq!(tokens_empty, vec!["Hello", "world"]);
    }

    #[test]
    fn test_boundary_with_punctuation() {
        let text = "Hello, world!";
        let tokens = tokenize_by_whitespace(text, "***");
        assert_eq!(tokens, vec!["***Hello***", "***world***"]);
    }

    #[test]
    fn test_filter_by_symbols_basic() {
        let mut syms = HashSet::new();
        syms.insert("hello".to_string());
        syms.insert("world".to_string());
        syms.insert("h".to_string());
        syms.insert("e".to_string());
        
        let input = "hello world!";
        let result = filter_by_symbols(input, &syms);
        assert_eq!(result, "helloworld");
    }

    #[test]
    fn test_filter_by_symbols_longest_match() {
        let mut syms = HashSet::new();
        syms.insert("a".to_string());
        syms.insert("ab".to_string());
        syms.insert("abc".to_string());
        syms.insert("b".to_string());
        syms.insert("c".to_string());
        
        let input = "abcdef";
        let result = filter_by_symbols(input, &syms);
        // Should prefer "abc" over "a" + "b" + "c"
        assert_eq!(result, "abc");
    }

    #[test]
    fn test_filter_by_symbols_overlapping() {
        let mut syms = HashSet::new();
        syms.insert("cat".to_string());
        syms.insert("at".to_string());
        syms.insert("dog".to_string());
        syms.insert("og".to_string());
        
        let input = "catdog";
        let result = filter_by_symbols(input, &syms);
        // Should prefer "cat" + "dog" over "cat" + "og" or other combinations
        assert_eq!(result, "catdog");
    }

    #[test]
    fn test_filter_by_symbols_no_matches() {
        let mut syms = HashSet::new();
        syms.insert("x".to_string());
        syms.insert("y".to_string());
        syms.insert("z".to_string());
        
        let input = "hello world";
        let result = filter_by_symbols(input, &syms);
        assert_eq!(result, "");
    }

    #[test]
    fn test_filter_by_symbols_partial_matches() {
        let mut syms = HashSet::new();
        syms.insert("h".to_string());
        syms.insert("e".to_string());
        syms.insert("l".to_string());
        syms.insert("o".to_string());
        
        let input = "hello world";
        let result = filter_by_symbols(input, &syms);
        // Should find: h-e-l-l-o (skip space and w) o (skip r) l (skip d)
        assert_eq!(result, "hellool");
    }

    #[test]
    fn test_filter_by_symbols_unicode() {
        let mut syms = HashSet::new();
        syms.insert("café".to_string());
        syms.insert("naïve".to_string());
        syms.insert("é".to_string());
        syms.insert("ï".to_string());
        
        let input = "café naïve résumé";
        let result = filter_by_symbols(input, &syms);
        // Should find: "café" (skip space) "naïve" (skip space and r) "é" (skip sum) "é"
        assert_eq!(result, "cafénaïveéé");
    }

    #[test]
    fn test_filter_by_symbols_empty_input() {
        let mut syms = HashSet::new();
        syms.insert("test".to_string());
        
        let input = "";
        let result = filter_by_symbols(input, &syms);
        assert_eq!(result, "");
    }

    #[test]
    fn test_filter_by_symbols_empty_set() {
        let syms = HashSet::new();
        
        let input = "hello world";
        let result = filter_by_symbols(input, &syms);
        assert_eq!(result, "");
    }

    #[test]
    fn test_filter_by_symbols_single_chars() {
        let mut syms = HashSet::new();
        syms.insert("a".to_string());
        syms.insert("b".to_string());
        syms.insert("c".to_string());
        
        let input = "abcdefabc";
        let result = filter_by_symbols(input, &syms);
        assert_eq!(result, "abcabc");
    }

    #[test]
    fn test_filter_by_symbols_complex_overlapping() {
        let mut syms = HashSet::new();
        syms.insert("the".to_string());
        syms.insert("he".to_string());
        syms.insert("cat".to_string());
        syms.insert("at".to_string());
        syms.insert("t".to_string());
        
        let input = "thecat";
        let result = filter_by_symbols(input, &syms);
        // Should prefer "the" + "cat" over other combinations
        assert_eq!(result, "thecat");
    }
}