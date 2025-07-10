//! Epitran module for phonetic transliteration using compiled wFSTs
//!
//! This module provides functionality to transliterate text from orthographic
//! representations to phonetic representations using weighted finite state transducers
//! (wFSTs) that are compiled at build time.

use anyhow::{Context, Result};
use parserule::rulefst::apply_fst;
use rustfst::fst_impls::VectorFst;
use rustfst::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;

// Include the generated FST data
include!(concat!(env!("OUT_DIR"), "/compiled_fsts.rs"));

/// Main struct for handling phonetic transliteration
///
/// Contains all compiled wFSTs for supported languages and provides
/// methods for transliterating text.
pub struct Epitran {
    fsts: &'static CompiledFstMap,
}

impl Epitran {
    /// Create a new Epitran instance
    ///
    /// This initializes the transliterator with all compiled language FSTs.
    pub fn new() -> Self {
        Self {
            fsts: &COMPILED_FSTS,
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
        self.fsts.contains_key(lang_code)
    }

    /// Transliterate text from orthographic to phonetic representation
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
        let (symt, fst) = self
            .fsts
            .get(lang_code)
            .with_context(|| format!("Language '{lang_code}' is not supported"))?;

        // Prepare input with boundaries
        let input = format!("{boundary}{text}{boundary}");

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
    /// # Arguments
    /// * `lang_code` - The language-script code
    ///
    /// # Returns
    /// A tuple containing the symbol table and FST for the language, if available
    pub fn get_language_fst(
        &self,
        lang_code: &str,
    ) -> Option<&(Arc<SymbolTable>, VectorFst<TropicalWeight>)> {
        self.fsts.get(lang_code)
    }
}

impl Default for Epitran {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    // use super::*;

    // #[test]
    // fn test_epitran_creation() {
    //     let epitran = Epitran::new();
    //     assert!(!epitran.available_languages().is_empty());
    // }

    // #[test]
    // fn test_language_support_check() {
    //     let epitran = Epitran::new();

    //     // Test with a non-existent language
    //     assert!(!epitran.is_language_supported("nonexistent_Lang"));

    //     // Test with available languages (if any)
    //     for &lang in epitran.available_languages() {
    //         assert!(epitran.is_language_supported(lang));
    //     }
    // }

    // #[test]
    // fn test_transliterate_unsupported_language() {
    //     let epitran = Epitran::new();
    //     let result = epitran.transliterate("nonexistent_Lang", "#", "test");
    //     assert!(result.is_err());
    // }

    // #[test]
    // fn test_transliterate_empty_text() {
    //     let epitran = Epitran::new();

    //     // Test with first available language if any exist
    //     if let Some(&lang) = epitran.available_languages().first() {
    //         let result = epitran.transliterate(lang, "#", "");
    //         assert!(result.is_ok());
    //     }
    // }

    // #[test]
    // fn test_simple_transliterate() {
    //     let epitran = Epitran::new();

    //     // Test with first available language if any exist
    //     // if let Some(&lang) = epitran.available_languages().first() {
    //     //     let result = epitran.transliterate_simple(lang, "test");
    //     //     assert!(result.is_ok());
    //     let result = epitran.transliterate_simple("spa_Latn", "villa");
    //     assert!(result.is_ok());
    //     // }
    // }

    // #[test]
    // fn test_simple_transliterate_villa() {
    //     let epitran = Epitran::new();

    //     // Test with first available language if any exist
    //     // if let Some(&lang) = epitran.available_languages().first() {
    //     //     let result = epitran.transliterate_simple(lang, "test");
    //     //     assert!(result.is_ok());
    //     let output = epitran
    //         .transliterate_simple("spa_Latn", "villa")
    //         .expect("Couldn't transliterate 'villa'");
    //     assert_eq!(output, "biʝa".to_string());
    //     // }
    // }

    // #[test]
    // fn test_simple_transliterate_oui() {
    //     let epitran = Epitran::new();

    //     // Test with first available language if any exist
    //     // if let Some(&lang) = epitran.available_languages().first() {
    //     //     let result = epitran.transliterate_simple(lang, "test");
    //     //     assert!(result.is_ok());
    //     let output = epitran
    //         .transliterate_simple("fra_Latn", "oui")
    //         .expect("Couldn't transliterate 'oui'");
    //     assert_eq!(output, "wi".to_string());
    //     // }
    // }
}
