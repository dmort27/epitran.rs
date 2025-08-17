use csv::Reader;
use serde::Deserialize;
use std::collections::HashSet;
use std::error::Error;

use crate::graphemeparse::get_graphemes;
use crate::normalize::nfd_normalize;

#[derive(Debug, Deserialize, PartialEq)]
struct Mapping {
    orth: String,
    phon: String,
}
#[derive(Debug, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct ParsedMapping {
    pub orth: Vec<String>,
    pub phon: Vec<String>,
}

pub fn process_map(data: String) -> Result<(HashSet<String>, Vec<ParsedMapping>), Box<dyn Error>> {
    let mut parsed_rules = Vec::new();
    parsed_rules.push(ParsedMapping {
        orth: vec!["#".to_string()],
        phon: vec!["#".to_string()],
    }); // Add word boundary symbols
    let mut syms: HashSet<String> = HashSet::new();
    syms.insert("#".to_string()); // Add the super-final state symbol

    let mut reader = Reader::from_reader(data.as_bytes());
    for result in reader.deserialize() {
        let record: Mapping = result.unwrap_or_else(|e| {
            println!("{e}: Error reading CSV data for map files.");
            Mapping {
                orth: "".to_string(),
                phon: "".to_string(),
            }
        });
        // Normalize the orthographic and phonetic strings before processing
        let normalized_orth = nfd_normalize(&record.orth);
        let normalized_phon = nfd_normalize(&record.phon);
        
        let mut orth = get_graphemes(&normalized_orth);
        let mut phon = get_graphemes(&normalized_phon);
        syms.extend(orth.clone());
        syms.extend(phon.clone());
        let target_len = orth.len().max(phon.len());
        orth.resize(target_len, "".to_string());
        phon.resize(target_len, "".to_string());
        let parsed_mapping = ParsedMapping { orth, phon };
        parsed_rules.push(parsed_mapping);
    }
    Ok((syms, parsed_rules))
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::mapparse::{process_map, ParsedMapping};

    #[test]
    fn test_process_data() {
        let data = "orth,phon\na,a\nb,b\nab,c\n";
        let syms = HashSet::from([
            "#".to_string(),
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
        ]);
        let mapping = vec![
            ParsedMapping {
                orth: vec!["#".to_string()],
                phon: vec!["#".to_string()],
            },
            ParsedMapping {
                orth: vec!["a".to_string()],
                phon: vec!["a".to_string()],
            },
            ParsedMapping {
                orth: vec!["b".to_string()],
                phon: vec!["b".to_string()],
            },
            ParsedMapping {
                orth: vec!["a".to_string(), "b".to_string()],
                phon: vec!["c".to_string(), "".to_string()],
            },
        ];
        assert_eq!(
            process_map(data.to_string()).expect("Failed to process map data in test"),
            (syms, mapping)
        );
    }

    #[test]
    fn test_process_data_with_uni_esc() {
        let data = "orth,phon\na,a\nb,b\nab,\\u0250\n";
        let syms = HashSet::from([
            "#".to_string(),
            "a".to_string(),
            "b".to_string(),
            "ɐ".to_string(),
        ]);
        let mapping = vec![
            ParsedMapping {
                orth: vec!["#".to_string()],
                phon: vec!["#".to_string()],
            },
            ParsedMapping {
                orth: vec!["a".to_string()],
                phon: vec!["a".to_string()],
            },
            ParsedMapping {
                orth: vec!["b".to_string()],
                phon: vec!["b".to_string()],
            },
            ParsedMapping {
                orth: vec!["a".to_string(), "b".to_string()],
                phon: vec!["ɐ".to_string(), "".to_string()],
            },
        ];
        assert_eq!(
            process_map(data.to_string())
                .expect("Failed to process map data with unicode escapes in test"),
            (syms, mapping)
        );
    }
}
