use anyhow::{Context, Result};
use std::env;
use std::fs;
use std::path::Path;
use walkdir::WalkDir;

fn main() -> Result<()> {
    println!("cargo:rerun-if-changed=data/");

    let out_dir = env::var("OUT_DIR")?;
    let dest_path = Path::new(&out_dir).join("compiled_fsts.rs");

    // Discover all language codes from map files
    let mut lang_codes = std::collections::HashSet::new();

    for entry in WalkDir::new("data/map").into_iter().filter_map(|e| e.ok()) {
        if let Some(file_name) = entry.file_name().to_str() {
            if file_name.ends_with(".csv") {
                if let Some(lang_code) = extract_lang_code(file_name) {
                    if true {
                        lang_codes.insert(lang_code);
                    }
                }
            }
        }
    }

    let mut generated_code = String::new();
    // generated_code.push_str("use std::collections::HashMap;\n");
    // generated_code.push_str("use std::sync::Arc;\n");
    // generated_code.push_str("use rustfst::prelude::*;\n");
    // generated_code.push_str("use rustfst::fst_impls::VectorFst;\n");
    generated_code.push_str("use once_cell::sync::Lazy;\n");
    generated_code.push_str("use parserule::langfst::build_lang_fst;\n\n");

    // Generate language data as static strings
    let mut successful_langs = Vec::new();
    let mut lang_data = Vec::new();

    for lang_code in &lang_codes {
        println!("\n+++ Building wFST for {lang_code}+++\n");
        match get_language_data(lang_code) {
            Ok((map_content, pre_content, post_content)) => {
                let var_prefix = lang_code.replace("-", "_").to_uppercase();
                let map_var = format!("MAP_DATA_{var_prefix}");
                let pre_var = format!("PRE_DATA_{var_prefix}");
                let post_var = format!("POST_DATA_{var_prefix}");

                generated_code.push_str(&format!(
                    "static {map_var}: Lazy<String> = Lazy::new(|| {map_content:?}.to_string());\n"
                ));
                generated_code.push_str(&format!(
                    "static {pre_var}: Lazy<String> = Lazy::new(|| {pre_content:?}.to_string());\n"
                ));
                generated_code.push_str(&format!(
                    "static {post_var}: Lazy<String> = Lazy::new(|| {post_content:?}.to_string());\n"
                ));

                lang_data.push((lang_code.clone(), map_var, pre_var, post_var));
                successful_langs.push(lang_code.clone());
            }
            Err(e) => {
                eprintln!("Warning: Failed to read data for {lang_code}: {e}");
            }
        }
    }

    // Generate type alias and the lazy static map that builds FSTs at runtime
    generated_code.push_str("\ntype CompiledFstMap = HashMap<String, (Arc<SymbolTable>, VectorFst<TropicalWeight>)>;\n\n");
    generated_code.push_str("pub static COMPILED_FSTS: Lazy<CompiledFstMap> = Lazy::new(|| {\n");
    generated_code.push_str("    let mut map = HashMap::new();\n");

    for (lang_code, map_var, pre_var, post_var) in &lang_data {
        let key = lang_code.replace("-", "_");
        generated_code.push_str(&format!(
            "    println!(\"+++Building WFST for {lang_code}\");\n    if let Ok((symt, fst)) = build_lang_fst((*{pre_var}).clone(), (*{post_var}).clone(), (*{map_var}).clone()) {{\n"
        ));
        generated_code.push_str(&format!(
            "        map.insert(\"{key}\".to_string(), (symt, fst));\n"
        ));
        generated_code.push_str(&format!(
            "    }} else {{\n        eprintln!(\"Warning: Failed to build FST for {lang_code}\");\n    }}\n"
        ));
    }

    generated_code.push_str("    map\n");
    generated_code.push_str("});\n\n");

    // Generate available languages list
    generated_code.push_str("pub static AVAILABLE_LANGUAGES: &[&str] = &[\n");
    for lang_code in &successful_langs {
        let key = lang_code.replace("-", "_");
        generated_code.push_str(&format!("    \"{key}\",\n"));
    }
    generated_code.push_str("];\n");

    fs::write(&dest_path, generated_code).context("Failed to write generated code")?;

    println!(
        "Successfully prepared {} language datasets",
        successful_langs.len()
    );

    Ok(())
}

fn extract_lang_code(filename: &str) -> Option<String> {
    filename.strip_suffix(".csv").map(|stem| stem.to_string())
}

fn get_language_data(lang_code: &str) -> Result<(String, String, String)> {
    // Read map file (required)
    let map_path = format!("data/map/{lang_code}.csv");
    let map_content = fs::read_to_string(&map_path)
        .with_context(|| format!("Failed to read map file: {map_path}"))?;

    // Read pre file (optional)
    let pre_path = format!("data/pre/{lang_code}.txt");
    let pre_content = fs::read_to_string(&pre_path).unwrap_or_default();

    // Read post file (optional)
    let post_path = format!("data/post/{lang_code}.txt");
    let post_content = fs::read_to_string(&post_path).unwrap_or_default();

    Ok((map_content, pre_content, post_content))
}
