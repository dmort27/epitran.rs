use csv::Reader;
use serde::Deserialize;
use std::error::Error;

use std::collections::HashSet;

use rustfst::fst_impls::VectorFst;
use rustfst::fst_traits::{CoreFst, ExpandedFst, MutableFst};
use rustfst::prelude::*;
use rustfst::utils::{acceptor, transducer};

use crate::graphemeparse::get_graphemes;

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

pub fn process_map(data: &str) -> Result<(HashSet<String>, Vec<ParsedMapping>), Box<dyn Error>> {
    let mut parsed_rules = Vec::new();
    let mut syms: HashSet<String> = HashSet::new();

    let mut reader = Reader::from_reader(data.as_bytes());
    for result in reader.deserialize() {
        let record: Mapping = result.unwrap_or_else(|e| {
            println!("{e}: Error reading CSV data.");
            Mapping {
                orth: "".to_string(),
                phon: "".to_string(),
            }
        });
        let mut orth = get_graphemes(&record.orth);
        let mut phon = get_graphemes(&record.phon);
        syms.extend(orth.clone());
        syms.extend(phon.clone());
        let target_len = orth.len().max(phon.len());
        orth.resize(target_len, "".to_string());
        phon.resize(target_len, "".to_string());
        let parsed_mapping = ParsedMapping {
            orth: orth,
            phon: phon,
        };
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
        let syms = HashSet::from(["a".to_string(), "b".to_string(), "c".to_string()]);
        let mapping = vec![
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
        assert_eq!(process_map(data).unwrap(), (syms, mapping));
    }

    fn test_process_data_with_uni_esc() {
        let data = "orth,phon\na,a\nb,b\nab,\\u0250\n";
        let syms = HashSet::from(["a".to_string(), "b".to_string(), "c".to_string()]);
        let mapping = vec![
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
        assert_eq!(process_map(data).unwrap(), (syms, mapping));
    }
}
