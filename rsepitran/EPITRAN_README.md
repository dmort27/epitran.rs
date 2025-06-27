# Epitran Module

The `epitran` module provides phonetic transliteration functionality using weighted finite state transducers (wFSTs) that are compiled at build time.

## Features

- **Compile-time FST generation**: All wFSTs are built during compilation from data files
- **Multiple language support**: Supports all language-script combinations found in the data directory
- **Graceful error handling**: Compilation continues even if some language files are incompatible
- **Lazy initialization**: FSTs are built on first access to minimize startup time
- **Boundary symbol support**: Configurable boundary symbols for transliteration

## Usage

```rust
use rsepitran::Epitran;

// Create a new Epitran instance
let epitran = Epitran::new();

// Check available languages
println!("Available languages: {:?}", epitran.available_languages());

// Transliterate text
match epitran.transliterate("fra_Latn", "#", "bonjour") {
    Ok(phonetic) => println!("Phonetic: {}", phonetic),
    Err(e) => eprintln!("Error: {}", e),
}

// Simple transliteration (uses "#" as default boundary)
let result = epitran.transliterate_simple("ara_Arab", "مرحبا")?;
```

## Data File Structure

The module expects data files in the following structure:

```
data/
├── map/           # Required mapping files (CSV format)
│   ├── ara-Arab.csv
│   ├── fra-Latn.csv
│   └── ...
├── pre/           # Optional preprocessing rules (TXT format)
│   ├── fra-Latn.txt
│   └── ...
└── post/          # Optional postprocessing rules (TXT format)
    ├── fra-Latn.txt
    └── ...
```

### File Naming Convention

- Files use the format: `<iso-639-3>-<script_code>.(csv|txt)`
- In the API, hyphens are converted to underscores (e.g., `ara-Arab` becomes `ara_Arab`)

### File Formats

- **Map files** (`.csv`): Contain orthographic to phonetic mappings with headers `Orth,Phon`
- **Pre files** (`.txt`): Contain preprocessing rules in the parserule format
- **Post files** (`.txt`): Contain postprocessing rules in the parserule format

## Build Process

The build script (`build.rs`) performs the following steps:

1. Scans the `data/map/` directory for available languages
2. For each language, reads the map file (required) and pre/post files (optional)
3. Generates static string data containing the file contents
4. Creates a lazy static HashMap that builds FSTs on first access
5. Handles compilation errors gracefully with warning messages

## Error Handling

- Missing map files cause the language to be skipped with a warning
- Missing pre/post files are treated as empty (no preprocessing/postprocessing)
- FST compilation errors are caught and logged, allowing other languages to compile successfully
- Runtime transliteration errors return `Result<String, anyhow::Error>`

## Performance Considerations

- FSTs are built lazily on first access to each language
- Once built, FSTs are cached in memory for subsequent use
- The build process embeds all data files as static strings in the binary
- Large numbers of languages may increase binary size and initial memory usage

## Dependencies

- `parserule`: For FST building and rule parsing
- `rustfst`: For finite state transducer operations
- `once_cell`: For lazy static initialization
- `anyhow`: For error handling