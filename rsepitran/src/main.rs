use rsepitran::tokenize_by_whitespace;

fn main() {
    // Test the tokenize_by_whitespace function
    let test_text = "Hello, world! This is a test. How are you?";
    let tokens = tokenize_by_whitespace(test_text);
    
    println!("Input: {}", test_text);
    println!("Tokens: {:?}", tokens);
    
    // Test with Unicode characters
    let unicode_text = "Héllo, wörld! Café naïve résumé.";
    let unicode_tokens = tokenize_by_whitespace(unicode_text);
    
    println!("\nUnicode input: {}", unicode_text);
    println!("Unicode tokens: {:?}", unicode_tokens);
}
