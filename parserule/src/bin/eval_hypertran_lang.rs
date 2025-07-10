use std::fs::read_to_string;

use csv::Reader;
use serde::Deserialize;

use colored::Colorize;

use parserule::langfst::build_lang_fst;
use parserule::rulefst::apply_fst;
use std::error::Error;

use clap::Parser;

use tabled::{settings::Style, Table, Tabled};

#[derive(Tabled)]
struct Prediction {
    input: String,
    predicted: String,
    reference: String,
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    #[arg(short = 'm', long = "map")]
    map: String,

    #[arg(short = 'p', long = "pre")]
    preproc: String,

    #[arg(short = 'P', long = "post")]
    postproc: String,

    #[arg(short = 't', long = "test")]
    testcases: String,
}

#[derive(Debug, Deserialize, PartialEq)]
struct TestCase {
    input: String,
    output: String,
}

fn main() -> Result<(), Box<dyn Error>> {
    let cli = Cli::parse();

    // Read map file
    let mapping: String = read_to_string(cli.map.clone()).unwrap_or_else(|e| {
        eprintln!(
            "{}",
            format!("{e}: Cannot open file '{}'.", cli.map).bold().red()
        );
        std::process::exit(1);
    });
    // println!("{mapping}");
    let preproc: String = read_to_string(cli.preproc.clone()).unwrap_or_else(|e| {
        eprintln!(
            "{}",
            format!("{e}: Cannot open file '{}'.", cli.preproc)
                .bold()
                .red()
        );
        std::process::exit(1);
    });
    let postproc: String = read_to_string(cli.postproc.clone()).unwrap_or_else(|e| {
        eprintln!(
            "{}",
            format!("{e}: Cannot open file '{}'.", cli.postproc)
                .bold()
                .red()
        );
        std::process::exit(1);
    });

    println!("{}", "Compiling wFST...".blue());

    let (symt, fst) = build_lang_fst(mapping, preproc, postproc)?;

    println!("{}", "Successfully compiled wFST".bold().green());

    let mut predictions: Vec<Prediction> = Vec::new();

    // Read test cases file
    let testcases_content: String = read_to_string(cli.testcases.clone()).unwrap_or_else(|e| {
        eprintln!(
            "{}",
            format!("{e}: Cannot open file '{}'.", cli.testcases)
                .bold()
                .red()
        );
        std::process::exit(1);
    });

    let mut reader = Reader::from_reader(testcases_content.as_bytes());
    let deserialized = reader.deserialize();
    for result in deserialized {
        let record: TestCase = result?;
        let predicted_form = apply_fst(symt.clone(), fst.clone(), record.input.clone());
        let input_form = record.input;
        let reference_form = record.output.clone();
        if predicted_form == record.output {
            predictions.push(Prediction {
                input: input_form,
                predicted: format!("{}", predicted_form.green()),
                reference: format!("{}", reference_form.purple()),
            });
        } else {
            predictions.push(Prediction {
                input: input_form,
                predicted: format!("{}", predicted_form.red()),
                reference: format!("{}", reference_form.purple()),
            });
        };
    }

    let mut table = Table::new(&predictions);
    table.with(Style::sharp());
    println!("{table}");

    Ok(())
}
