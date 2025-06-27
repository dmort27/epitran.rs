use rsepitran::{tokenize_by_whitespace, filter_by_symbols};
use std::collections::HashSet;

fn main() {
    // Test the tokenize_by_whitespace function
    let test_text = "Hello, world! This is a test. How are you?";
    let tokens = tokenize_by_whitespace(test_text, "#");
    
    println!("Input: {}", test_text);
    println!("Tokens with '#' boundary: {:?}", tokens);
    
    // Test with Unicode characters
    let unicode_text = "Héllo, wörld! Café naïve résumé.";
    let unicode_tokens = tokenize_by_whitespace(unicode_text, "|");
    
    println!("\nUnicode input: {}", unicode_text);
    println!("Unicode tokens with '|' boundary: {:?}", unicode_tokens);
    
    // Test with different boundaries
    let boundary_test = "Test different boundaries";
    println!("\nTesting different boundaries with: {}", boundary_test);
    
    let tokens_empty = tokenize_by_whitespace(boundary_test, "");
    println!("Empty boundary: {:?}", tokens_empty);
    
    let tokens_bracket = tokenize_by_whitespace(boundary_test, "<>");
    println!("'<>' boundary: {:?}", tokens_bracket);
    
    let tokens_star = tokenize_by_whitespace(boundary_test, "***");
    println!("'***' boundary: {:?}", tokens_star);
    
    // Test the filter_by_symbols function
    println!("\n=== Testing filter_by_symbols function ===");
    
    let mut syms = HashSet::new();
    syms.insert("hello".to_string());
    syms.insert("world".to_string());
    syms.insert("test".to_string());
    syms.insert("h".to_string());
    syms.insert("e".to_string());
    syms.insert("l".to_string());
    syms.insert("o".to_string());
    
    let filter_input = "hello world! this is a test.";
    let filtered = filter_by_symbols(filter_input, &syms);
    println!("Input: {}", filter_input);
    println!("Symbols: {:?}", syms);
    println!("Filtered: {}", filtered);
    
    // Test longest match preference
    let mut overlap_syms = HashSet::new();
    overlap_syms.insert("a".to_string());
    overlap_syms.insert("ab".to_string());
    overlap_syms.insert("abc".to_string());
    overlap_syms.insert("b".to_string());
    overlap_syms.insert("c".to_string());
    
    let overlap_input = "abcdef";
    let overlap_filtered = filter_by_symbols(overlap_input, &overlap_syms);
    println!("\nLongest match test:");
    println!("Input: {}", overlap_input);
    println!("Symbols: {:?}", overlap_syms);
    println!("Filtered (should prefer 'abc'): {}", overlap_filtered);
    
    // Test with Unicode
    let mut unicode_syms = HashSet::new();
    unicode_syms.insert("café".to_string());
    unicode_syms.insert("naïve".to_string());
    unicode_syms.insert("é".to_string());
    unicode_syms.insert("ï".to_string());
    
    let unicode_input = "café naïve résumé";
    let unicode_filtered = filter_by_symbols(unicode_input, &unicode_syms);
    println!("\nUnicode test:");
    println!("Input: {}", unicode_input);
    println!("Symbols: {:?}", unicode_syms);
    println!("Filtered: {}", unicode_filtered);
}
