use rsepitran::epitran::Epitran;
use unicode_normalization::UnicodeNormalization;

#[test]
fn test_nfd_normalization_integration() {
    // Test that the system can handle composed characters correctly
    // by ensuring they are normalized to NFD form
    
    let composed_text = "café"; // é is a single composed character
    let nfd_text: String = composed_text.nfd().collect();
    
    // Verify that NFD normalization actually changes the text
    assert!(nfd_text.len() > composed_text.len(), 
            "NFD should decompose é into e + combining accent");
    
    // Test that our normalize_input function works correctly
    let epitran = Epitran::new();
    let normalized = epitran.normalize_input(composed_text);
    
    // The normalized text should be in NFD form and lowercase
    assert_eq!(normalized, nfd_text.to_lowercase());
    
    println!("Original: {} (len: {})", composed_text, composed_text.len());
    println!("NFD:      {} (len: {})", nfd_text, nfd_text.len());
    println!("Normalized: {} (len: {})", normalized, normalized.len());
}

#[test]
fn test_multiple_composed_characters() {
    let epitran = Epitran::new();
    
    let test_cases = vec![
        "café",      // é -> e + combining acute
        "naïve",     // ï -> i + combining diaeresis  
        "résumé",    // é -> e + combining acute (twice)
        "piñata",    // ñ -> n + combining tilde
        "Zürich",    // ü -> u + combining diaeresis
    ];
    
    for case in test_cases {
        let normalized = epitran.normalize_input(case);
        let expected_nfd: String = case.nfd().collect::<String>().to_lowercase();
        
        assert_eq!(normalized, expected_nfd, 
                   "Failed to normalize '{}' correctly", case);
        
        println!("'{}' -> '{}' (len: {} -> {})", 
                 case, normalized, case.len(), normalized.len());
    }
}

#[test]
fn test_already_normalized_text() {
    let epitran = Epitran::new();
    
    // Test text that's already in NFD form
    let already_nfd = "cafe\u{0301}"; // e + combining acute accent
    let normalized = epitran.normalize_input(already_nfd);
    
    // Should remain the same (except for case conversion)
    assert_eq!(normalized, already_nfd.to_lowercase());
}

#[test]
fn test_mixed_scripts_normalization() {
    let epitran = Epitran::new();
    
    let test_cases = vec![
        "hello",      // ASCII - should remain unchanged
        "café",       // Latin with diacritics
        "naïve",      // Latin with diacritics
        "test123",    // ASCII with numbers
    ];
    
    for case in test_cases {
        let normalized = epitran.normalize_input(case);
        let expected: String = case.nfd().collect::<String>().to_lowercase();
        
        assert_eq!(normalized, expected, 
                   "Failed to normalize mixed script text '{}'", case);
    }
}