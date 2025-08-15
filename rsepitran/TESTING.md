# Epitran Testing Framework

This document describes the `hypertran_test` binary, a comprehensive testing framework for the rsepitran library.

## Overview

The testing framework automatically tests each language that has:
1. A CSV mapping file in `data/map/` (excluding files with `.excl` extension)
2. A corresponding test file in `data/tests/`

## Features

- **Automated Testing**: Loads test cases from CSV files and runs transliteration
- **Visual Results**: Displays results in formatted tables with color coding:
  - 🔵 Blue text: Correct translations (hypothesis matches reference)
  - 🔴 Red text: Incorrect translations (hypothesis differs from reference)
- **Comprehensive Statistics**: Provides detailed accuracy metrics per language and overall
- **Flexible Execution**: Supports both demo mode and full testing

## Usage

### Demo Mode (Recommended for Testing)
```bash
# Test all languages with mock data
cargo run --bin hypertran_test -- --demo

# Test specific language with mock data
cargo run --bin hypertran_test -- --demo --lang fra_Latn
cargo run --bin hypertran_test -- --demo -l spa_Latn
```
- Runs quickly with mock data
- Shows the framework structure and table formatting
- Perfect for verifying the implementation works
- Supports language-specific demo data for common languages

### Full Testing Mode
```bash
# Test all available languages
cargo run --bin hypertran_test

# Test only a specific language
cargo run --bin hypertran_test -- --lang deu_Latn
cargo run --bin hypertran_test -- -l fra_Latn
```
- Compiles FSTs for specified languages (takes significant time)
- Runs real transliteration tests
- Provides actual accuracy measurements
- Use `--lang` option to test only one language for faster execution

## Test File Format

Test files in `data/tests/` should be CSV files with the format:
```csv
input,output
word1,phonetic1
word2,phonetic2
...
```

Example (`deu_Latn-tests.csv`):
```csv
input,output
da,daː
Abend,aːbn̩t
Sprache,ʃpraːxə
Pass,pas
quälen,kvɛːlən
```

## Output Format

The framework provides:

1. **Per-language tables** showing input-hypothesis-reference triples
2. **Per-language statistics** with item counts and accuracy percentages
3. **Summary statistics** including:
   - Test items per language
   - Accuracy per language (sorted by performance)
   - Overall accuracy across all languages

## Command-Line Options

- `--demo`: Run in demo mode with mock data (fast execution)
- `--lang <LANGUAGE>` or `-l <LANGUAGE>`: Test only a specific language
- `--help` or `-h`: Show help message with all available options

## Implementation Details

The framework:
- Uses `Epitran::available_languages()` to get supported language codes
- Converts language codes from underscore format (`fra_Latn`) to test file format (`fra_Latn-tests.csv`)
- Calls `epitran.transliterate_simple(lang_code, input)` for each test case
- Compares system output (hypothesis) against reference translations
- Uses the `tabled` crate for table formatting and `colored` crate for text coloring
- Supports filtering to test only specific languages for faster execution

## Dependencies

The testing framework requires:
- `tabled = "0.15"` - For table formatting
- `colored = "3.0.0"` - For colored terminal output
- `anyhow` - For error handling
- `rsepitran` - The main library being tested