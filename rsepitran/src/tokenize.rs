use unicode_segmentation::UnicodeSegmentation;

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
}