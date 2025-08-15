//! Epitran module for phonetic transliteration using lazily compiled wFSTs
//!
//! This module provides functionality to transliterate text from orthographic
//! representations to phonetic representations using weighted finite state transducers
//! (wFSTs) that are compiled on-demand at runtime and cached in memory.

use anyhow::Result;
use once_cell::sync::OnceCell;
use parserule::langfst::build_lang_fst;
use parserule::rulefst::apply_fst;
use rustfst::fst_impls::VectorFst;
use rustfst::prelude::*;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// Include the generated language data
include!(concat!(env!("OUT_DIR"), "/language_data.rs"));

/// Cached FST data for a language
type CachedFst = (Arc<SymbolTable>, VectorFst<TropicalWeight>);

/// Main struct for handling phonetic transliteration
///
/// Contains lazily compiled wFSTs for supported languages and provides
/// methods for transliterating text. FSTs are built on-demand when first
/// requested and cached in memory for subsequent use.
pub struct Epitran {
    fst_cache: Arc<Mutex<HashMap<String, Arc<OnceCell<Result<CachedFst, String>>>>>>,
}

impl Epitran {
    /// Create a new Epitran instance
    ///
    /// This initializes the transliterator with an empty FST cache.
    /// FSTs will be compiled lazily when first requested.
    pub fn new() -> Self {
        Self {
            fst_cache: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Get a list of all available language codes
    ///
    /// Returns a slice of language-script codes that can be used for transliteration.
    /// The codes are in the format "iso639_3_script_code" (with underscores instead of hyphens).
    pub fn available_languages(&self) -> &'static [&'static str] {
        AVAILABLE_LANGUAGES
    }

    /// Check if a language is supported
    ///
    /// # Arguments
    /// * `lang_code` - The language-script code to check
    ///
    /// # Returns
    /// `true` if the language is supported, `false` otherwise
    pub fn is_language_supported(&self, lang_code: &str) -> bool {
        get_language_data(lang_code).is_some()
    }

    /// Get or build the FST for a specific language
    ///
    /// This method implements lazy compilation: if the FST for the requested language
    /// hasn't been built yet, it will be compiled and cached. Subsequent requests
    /// for the same language will use the cached FST.
    ///
    /// # Arguments
    /// * `lang_code` - The language-script code
    ///
    /// # Returns
    /// A reference to the cached FST data, or an error if compilation failed
    fn get_or_build_fst(&self, lang_code: &str) -> Result<Arc<CachedFst>> {
        // First, check if we already have a OnceCell for this language
        let cell = {
            let mut cache = self.fst_cache.lock().unwrap();
            cache
                .entry(lang_code.to_string())
                .or_insert_with(|| Arc::new(OnceCell::new()))
                .clone()
        };

        // Use get_or_init to ensure the FST is built only once
        let result = cell.get_or_init(|| {
            println!("Building FST for language: {}", lang_code);
            
            match get_language_data(lang_code) {
                Some((pre_content, post_content, map_content)) => {
                    match build_lang_fst(
                        pre_content.to_string(),
                        post_content.to_string(),
                        map_content.to_string(),
                    ) {
                        Ok((symt, fst)) => Ok((symt, fst)),
                        Err(e) => Err(format!("Failed to build FST for {}: {}", lang_code, e)),
                    }
                }
                None => Err(format!("Language '{}' is not supported", lang_code)),
            }
        });

        match result {
            Ok(fst_data) => Ok(Arc::new(fst_data.clone())),
            Err(e) => Err(anyhow::anyhow!("{}", e)),
        }
    }

    /// Transliterate text from orthographic to phonetic representation
    ///
    /// This method lazily compiles the FST for the requested language if it hasn't
    /// been built yet, then caches it for future use.
    ///
    /// # Arguments
    /// * `lang_code` - The language-script code (e.g., "ara_Arab", "fra_Latn")
    /// * `boundary` - The boundary symbol to use (typically "#")
    /// * `text` - The text to transliterate
    ///
    /// # Returns
    /// The transliterated text as a `Result<String, anyhow::Error>`
    ///
    /// # Example
    /// ```rust,no_run
    /// use rsepitran::epitran::Epitran;
    ///
    /// let epitran = Epitran::new();
    /// let result = epitran.transliterate("fra_Latn", "#", "bonjour");
    /// match result {
    ///     Ok(phonetic) => println!("Phonetic: {}", phonetic),
    ///     Err(e) => eprintln!("Error: {}", e),
    /// }
    /// ```
    pub fn transliterate(&self, lang_code: &str, boundary: &str, text: &str) -> Result<String> {
        // Get or build the FST for this language
        let fst_data = self.get_or_build_fst(lang_code)?;
        let (symt, fst) = fst_data.as_ref();

        // Prepare input with boundaries
        let input = format!("{}{}{}", boundary, text, boundary);

        // Apply the FST
        let result = apply_fst(symt.clone(), fst.clone(), input);

        // Remove boundaries from output if they exist
        let cleaned_result = if result.starts_with(boundary) && result.ends_with(boundary) {
            let start = boundary.len();
            let end = result.len() - boundary.len();
            if end > start {
                result[start..end].to_string()
            } else {
                String::new()
            }
        } else {
            result
        };

        Ok(cleaned_result)
    }

    /// Transliterate text without boundary symbols
    ///
    /// This is a convenience method that uses "#" as the default boundary symbol.
    /// The FST for the requested language will be compiled lazily if needed.
    ///
    /// # Arguments
    /// * `lang_code` - The language-script code
    /// * `text` - The text to transliterate
    ///
    /// # Returns
    /// The transliterated text as a `Result<String, anyhow::Error>`
    pub fn transliterate_simple(&self, lang_code: &str, text: &str) -> Result<String> {
        self.transliterate(lang_code, "#", text)
    }

    /// Get information about a specific language
    ///
    /// This method will compile the FST for the language if it hasn't been built yet.
    ///
    /// # Arguments
    /// * `lang_code` - The language-script code
    ///
    /// # Returns
    /// A reference to the cached FST data for the language, if available
    pub fn get_language_fst(&self, lang_code: &str) -> Result<Arc<CachedFst>> {
        self.get_or_build_fst(lang_code)
    }

    /// Check if a language's FST is already cached in memory
    ///
    /// # Arguments
    /// * `lang_code` - The language-script code
    ///
    /// # Returns
    /// `true` if the FST is already compiled and cached, `false` otherwise
    pub fn is_language_cached(&self, lang_code: &str) -> bool {
        let cache = self.fst_cache.lock().unwrap();
        if let Some(cell) = cache.get(lang_code) {
            cell.get().is_some()
        } else {
            false
        }
    }

    /// Get statistics about the current FST cache
    ///
    /// # Returns
    /// A tuple containing (total_supported_languages, cached_languages)
    pub fn cache_stats(&self) -> (usize, usize) {
        let cache = self.fst_cache.lock().unwrap();
        let cached_count = cache.values().filter(|cell| cell.get().is_some()).count();
        (AVAILABLE_LANGUAGES.len(), cached_count)
    }
}

impl Default for Epitran {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_epitran_creation() {
        let epitran = Epitran::new();
        assert!(!epitran.available_languages().is_empty());
        
        // Initially, no FSTs should be cached
        let (total, cached) = epitran.cache_stats();
        assert!(total > 0);
        assert_eq!(cached, 0);
    }

    #[test]
    fn test_language_support_check() {
        let epitran = Epitran::new();

        // Test with a non-existent language
        assert!(!epitran.is_language_supported("nonexistent_Lang"));

        // Test with available languages (if any)
        for &lang in epitran.available_languages() {
            assert!(epitran.is_language_supported(lang));
        }
    }

    #[test]
    fn test_transliterate_unsupported_language() {
        let epitran = Epitran::new();
        let result = epitran.transliterate("nonexistent_Lang", "#", "test");
        assert!(result.is_err());
    }

    #[test]
    fn test_lazy_compilation() {
        let epitran = Epitran::new();
        
        // Initially, Spanish should not be cached
        assert!(!epitran.is_language_cached("spa_Latn"));
        
        // After first use, it should be cached
        let result = epitran.transliterate_simple("spa_Latn", "villa");
        assert!(result.is_ok());
        assert!(epitran.is_language_cached("spa_Latn"));
        
        // Cache stats should reflect one cached language
        let (total, cached) = epitran.cache_stats();
        assert!(total > 0);
        assert_eq!(cached, 1);
    }

    #[test]
    fn test_simple_transliterate() {
        let epitran = Epitran::new();
        let result = epitran.transliterate_simple("spa_Latn", "villa");
        assert!(result.is_ok());
    }

    #[test]
    fn test_simple_transliterate_villa() {
        let epitran = Epitran::new();
        let output = epitran
            .transliterate_simple("spa_Latn", "villa")
            .expect("Couldn't transliterate 'villa'");
        assert_eq!(output, "biʝa".to_string());
    }

    #[test]
    fn test_simple_transliterate_oui() {
        let epitran = Epitran::new();
        let output = epitran
            .transliterate_simple("fra_Latn", "oui")
            .expect("Couldn't transliterate 'oui'");
        assert_eq!(output, "wi".to_string());
    }

    #[test]
    fn test_multiple_languages_cached_independently() {
        let epitran = Epitran::new();
        
        // Test that different languages are cached independently
        assert!(!epitran.is_language_cached("spa_Latn"));
        assert!(!epitran.is_language_cached("fra_Latn"));
        
        // Use Spanish
        let _ = epitran.transliterate_simple("spa_Latn", "hola");
        assert!(epitran.is_language_cached("spa_Latn"));
        assert!(!epitran.is_language_cached("fra_Latn"));
        
        // Use French
        let _ = epitran.transliterate_simple("fra_Latn", "bonjour");
        assert!(epitran.is_language_cached("spa_Latn"));
        assert!(epitran.is_language_cached("fra_Latn"));
        
        // Cache stats should show 2 cached languages
        let (_, cached) = epitran.cache_stats();
        assert_eq!(cached, 2);
    }
}
