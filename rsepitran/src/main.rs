use rsepitran::tokenize_by_whitespace;

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
}
