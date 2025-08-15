//! Epitran Testing Framework
//!
//! This binary provides a comprehensive testing framework for the rsepitran library.
//! It tests each language that has both a CSV file in `data/map` (excluding .excl files)
//! and a corresponding test file in `data/tests/`.
//!
//! Features:
//! - Loads test cases from CSV files with input/output pairs
//! - Uses the `transliterate_simple` method to generate hypotheses
//! - Compares system output against reference translations
//! - Displays results in colored tables (blue=correct, red=incorrect)
//! - Provides detailed accuracy statistics per language and overall
//!
//! Usage:
//! - `cargo run --bin hypertran_test --demo` - Run with mock data (fast)
//! - `cargo run --bin hypertran_test --demo --lang fra_Latn` - Demo specific language
//! - `cargo run --bin hypertran_test` - Run real tests (requires FST compilation)
//! - `cargo run --bin hypertran_test --lang deu_Latn` - Test specific language only

use anyhow::{Context, Result};
use clap::Parser;
use colored::*;
use rsepitran::epitran::Epitran;
use std::collections::HashMap;
use std::fs;
use std::path::Path;
use tabled::{settings::Style, Table, Tabled};
use unicode_normalization::UnicodeNormalization;

/// Normalize text using NFD (Normalized Form Decomposition)
/// This ensures all language data is consistently normalized
fn nfd_normalize(text: &str) -> String {
    text.nfd().collect()
}

#[derive(Parser)]
#[command(name = "hypertran_test")]
#[command(about = "Comprehensive testing framework for rsepitran library")]
struct Args {
    /// Run in demo mode with mock data (fast)
    #[arg(long)]
    demo: bool,
    
    /// Test only a specific language (e.g., deu_Latn, fra_Latn)
    #[arg(short = 'l', long = "lang")]
    language: Option<String>,
}

#[derive(Tabled)]
struct TestResult {
    #[tabled(rename = "Input")]
    input: String,
    #[tabled(rename = "Hypothesis")]
    hypothesis: String,
    #[tabled(rename = "Reference")]
    reference: String,
}

#[derive(Debug)]
struct LanguageStats {
    total_items: usize,
    correct_items: usize,
    accuracy: f64,
}

fn main() -> Result<()> {
    let args = Args::parse();
    
    println!("Running Epitran Test Suite");
    println!("==========================\n");
    
    if args.demo {
        println!("Note: Running in demo mode with mock data.");
        println!("Use without --demo flag to run real tests (requires FST compilation).\n");
        
        // Demo with mock data to show the table structure and functionality
        run_demo_test(args.language.as_deref())?;
        
        // Show what the real implementation would do:
        println!("\n{}", "REAL IMPLEMENTATION WOULD:".bold().underline());
        println!("1. Initialize Epitran with: let epitran = Epitran::new();");
        println!("2. Get available languages with: epitran.available_languages()");
        if let Some(lang) = &args.language {
            println!("3. Test only the specified language: {}", lang);
        } else {
            println!("3. For each language with a corresponding test file:");
        }
        println!("   - Load test cases from data/tests/{{lang_code}}-tests.csv");
        println!("   - Run epitran.transliterate_simple(lang_code, input)");
        println!("   - Compare output with reference");
        println!("   - Display results in colored table");
        println!("4. Provide summary statistics");
    } else {
        println!("Initializing Epitran (this may take some time to build FSTs)...");
        run_real_tests(args.language.as_deref())?;
    }
    
    Ok(())
}

fn run_real_tests(target_language: Option<&str>) -> Result<()> {
    let epitran = Epitran::new();
    let available_languages = epitran.available_languages();
    
    let mut all_stats: HashMap<String, LanguageStats> = HashMap::new();
    let mut total_items = 0;
    let mut total_correct = 0;
    let mut _tested_languages = 0;
    
    // Filter languages based on target_language parameter
    let languages_to_test: Vec<&str> = if let Some(target_lang) = target_language {
        if available_languages.contains(&target_lang) {
            vec![target_lang]
        } else {
            eprintln!("Error: Language '{}' is not available.", target_lang);
            eprintln!("Available languages: {:?}", available_languages);
            return Ok(());
        }
    } else {
        available_languages.to_vec()
    };
    
    for &lang_code in &languages_to_test {
        // Convert from underscore format (e.g., "fra_Latn") to hyphen format (e.g., "fra_Latn-tests.csv")
        let test_file_name = format!("{}-tests.csv", lang_code);
        let test_file_path = format!("data/tests/{}", test_file_name);
        
        if !Path::new(&test_file_path).exists() {
            if target_language.is_some() {
                eprintln!("Error: Test file '{}' not found for language '{}'.", test_file_path, lang_code);
                return Ok(());
            }
            continue;
        }
        
        println!("Testing language: {}", lang_code.bold());
        println!("{}", "=".repeat(50));
        
        match run_language_test(&epitran, lang_code, &test_file_path) {
            Ok(stats) => {
                total_items += stats.total_items;
                total_correct += stats.correct_items;
                all_stats.insert(lang_code.to_string(), stats);
                _tested_languages += 1;
            }
            Err(e) => {
                eprintln!("Error testing {}: {}", lang_code, e);
            }
        }
        
        println!();
    }
    
    // Print summary statistics
    print_summary_statistics(&all_stats, total_items, total_correct);
    
    Ok(())
}

fn run_demo_test(target_language: Option<&str>) -> Result<()> {
    let demo_lang = target_language.unwrap_or("deu_Latn");
    
    println!("Testing language: {}", demo_lang.bold());
    println!("{}", "=".repeat(50));
    
    // Mock test data to demonstrate the table structure
    // Use different demo data based on the language
    let demo_cases = match demo_lang {
        "fra_Latn" => vec![
            ("bonjour", "bonʒuʁ", "bonʒuʁ"),     // Correct
            ("chat", "ʃa", "ʃat"),               // Incorrect
            ("eau", "o", "o"),                   // Correct
            ("français", "fʁɑ̃sɛ", "fʁɑ̃se"),      // Incorrect
            ("merci", "mɛʁsi", "mɛʁsi"),         // Correct
        ],
        "spa_Latn" => vec![
            ("hola", "ola", "ola"),              // Correct
            ("casa", "kasa", "casa"),            // Incorrect
            ("niño", "niɲo", "niɲo"),            // Correct
            ("agua", "aɣwa", "aɣua"),            // Incorrect
            ("gracias", "gɾaθjas", "gɾaθjas"),   // Correct
        ],
        _ => vec![
            ("da", "daː", "daː"),                // Correct
            ("Abend", "aːbn̩t", "aːbənt"),        // Incorrect  
            ("Sprache", "ʃpraːxə", "ʃpraːxə"),   // Correct
            ("Pass", "pas", "pɑs"),              // Incorrect
            ("quälen", "kvɛːlən", "kvɛːlən"),    // Correct
        ],
    };
    
    let mut test_results = Vec::new();
    let mut correct_count = 0;
    let total_count = demo_cases.len();
    
    for (input, hypothesis, reference) in demo_cases {
        let is_correct = hypothesis == reference;
        if is_correct {
            correct_count += 1;
        }
        
        // Color the hypothesis based on correctness
        let colored_hypothesis = if is_correct {
            hypothesis.blue().to_string()
        } else {
            hypothesis.red().to_string()
        };
        
        test_results.push(TestResult {
            input: input.to_string(),
            hypothesis: colored_hypothesis,
            reference: reference.to_string(),
        });
    }
    
    // Display results table
    let table = Table::new(&test_results)
        .with(Style::modern())
        .to_string();
    println!("{}", table);
    
    let accuracy = (correct_count as f64 / total_count as f64) * 100.0;
    
    println!("Language: {} | Items: {} | Correct: {} | Accuracy: {:.2}%", 
             demo_lang, total_count, correct_count, accuracy);
    
    // Demo summary statistics
    println!("\n{}", "DEMO SUMMARY STATISTICS".bold().underline());
    println!("{}", "=".repeat(50));
    
    println!("\n{}", "Test items per language:".bold());
    println!("  {}: {} items", demo_lang, total_count);
    
    println!("\n{}", "Accuracy per language:".bold());
    let accuracy_str = format!("{:.2}%", accuracy);
    let colored_accuracy = if accuracy >= 90.0 {
        accuracy_str.green()
    } else if accuracy >= 70.0 {
        accuracy_str.yellow()
    } else {
        accuracy_str.red()
    };
    
    println!("  {}: {} ({}/{})", demo_lang, colored_accuracy, correct_count, total_count);
    
    println!("\n{}", "Overall Statistics:".bold());
    println!("  Total test items: {}", total_count);
    println!("  Total correct: {}", correct_count);
    println!("  Overall accuracy: {:.2}%", accuracy);
    
    let overall_accuracy_str = format!("{:.2}%", accuracy);
    let colored_overall = if accuracy >= 90.0 {
        overall_accuracy_str.green()
    } else if accuracy >= 70.0 {
        overall_accuracy_str.yellow()
    } else {
        overall_accuracy_str.red()
    };
    
    println!("\n{}: {}", "OVERALL ACCURACY".bold(), colored_overall.bold());
    
    Ok(())
}

fn run_language_test(epitran: &Epitran, lang_code: &str, test_file_path: &str) -> Result<LanguageStats> {
    let content = fs::read_to_string(test_file_path)
        .with_context(|| format!("Failed to read test file: {}", test_file_path))?;
    
    let mut test_results = Vec::new();
    let mut correct_count = 0;
    let mut total_count = 0;
    
    // Skip header line and process each test case
    for (line_num, line) in content.lines().enumerate().skip(1) {
        if line.trim().is_empty() {
            continue;
        }
        
        let parts: Vec<&str> = line.split(',').collect();
        if parts.len() != 2 {
            eprintln!("Warning: Invalid line format at line {}: {}", line_num + 1, line);
            continue;
        }
        
        let input = nfd_normalize(parts[0].trim());
        let reference = nfd_normalize(parts[1].trim());
        
        if input.is_empty() {
            continue;
        }
        
        // Get hypothesis from epitran
        let hypothesis = match epitran.transliterate_simple(lang_code, &input) {
            Ok(result) => result,
            Err(e) => {
                eprintln!("Error transliterating '{}': {}", input, e);
                continue;
            }
        };
        
        let is_correct = hypothesis == reference;
        if is_correct {
            correct_count += 1;
        }
        total_count += 1;
        
        // Color the hypothesis based on correctness
        let colored_hypothesis = if is_correct {
            hypothesis.blue().to_string()
        } else {
            hypothesis.red().to_string()
        };
        
        test_results.push(TestResult {
            input: input.to_string(),
            hypothesis: colored_hypothesis,
            reference: reference.to_string(),
        });
    }
    
    // Display results table
    if !test_results.is_empty() {
        let table = Table::new(&test_results)
            .with(Style::modern())
            .to_string();
        println!("{}", table);
    }
    
    let accuracy = if total_count > 0 {
        (correct_count as f64 / total_count as f64) * 100.0
    } else {
        0.0
    };
    
    println!("Language: {} | Items: {} | Correct: {} | Accuracy: {:.2}%", 
             lang_code, total_count, correct_count, accuracy);
    
    Ok(LanguageStats {
        total_items: total_count,
        correct_items: correct_count,
        accuracy,
    })
}

fn print_summary_statistics(all_stats: &HashMap<String, LanguageStats>, total_items: usize, total_correct: usize) {
    println!("\n{}", "SUMMARY STATISTICS".bold().underline());
    println!("{}", "=".repeat(50));
    
    println!("\n{}", "Test items per language:".bold());
    let mut lang_items: Vec<_> = all_stats.iter().collect();
    lang_items.sort_by_key(|(lang, _)| *lang);
    
    for (lang_code, stats) in &lang_items {
        println!("  {}: {} items", lang_code, stats.total_items);
    }
    
    println!("\n{}", "Accuracy per language:".bold());
    let mut lang_accuracy: Vec<_> = all_stats.iter().collect();
    lang_accuracy.sort_by(|(_, a), (_, b)| b.accuracy.partial_cmp(&a.accuracy).unwrap());
    
    for (lang_code, stats) in &lang_accuracy {
        let accuracy_str = format!("{:.2}%", stats.accuracy);
        let colored_accuracy = if stats.accuracy >= 90.0 {
            accuracy_str.green()
        } else if stats.accuracy >= 70.0 {
            accuracy_str.yellow()
        } else {
            accuracy_str.red()
        };
        
        println!("  {}: {} ({}/{})", 
                 lang_code, 
                 colored_accuracy, 
                 stats.correct_items, 
                 stats.total_items);
    }
    
    let overall_accuracy = if total_items > 0 {
        (total_correct as f64 / total_items as f64) * 100.0
    } else {
        0.0
    };
    
    println!("\n{}", "Overall Statistics:".bold());
    println!("  Total test items: {}", total_items);
    println!("  Total correct: {}", total_correct);
    println!("  Overall accuracy: {:.2}%", overall_accuracy);
    
    let overall_accuracy_str = format!("{:.2}%", overall_accuracy);
    let colored_overall = if overall_accuracy >= 90.0 {
        overall_accuracy_str.green()
    } else if overall_accuracy >= 70.0 {
        overall_accuracy_str.yellow()
    } else {
        overall_accuracy_str.red()
    };
    
    println!("\n{}: {}", "OVERALL ACCURACY".bold(), colored_overall.bold());
}