use std::fs::read_to_string;

use csv::Reader;
use serde::Deserialize;

use colored::Colorize;

use parserule::langfst::build_lang_fst;
use parserule::rulefst::apply_fst;
use std::error::Error;

use clap::Parser;

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
    let mapping: String = read_to_string(cli.map).unwrap();
    let preproc: String = read_to_string(cli.preproc).unwrap();
    let postproc: String = read_to_string(cli.postproc).unwrap();

    println!("{}", "Compiling wFST...".blue());

    let (symt, fst) = build_lang_fst(mapping, preproc, postproc)?;

    println!("{}", "Successfully compiled wFST".bold().green());

    let mut reader = Reader::from_reader(cli.testcases.as_bytes());
    for result in reader.deserialize() {
        let record: TestCase = result?;
        let prediction = apply_fst(symt.clone(), fst.clone(), record.input);
        let analysis = if prediction == record.output {
            format!("{} ({})", prediction.green(), record.output.purple())
        } else {
            format!("{} ({})", prediction.red(), record.output.purple())
        };
        println!("{}", analysis);
    }

    Ok(())
}
