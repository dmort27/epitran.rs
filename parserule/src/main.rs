mod ruleparse;
mod rulefst;

use itertools::enumerate;
use rustfst::{prelude::SerializableFst, DrawingConfig};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let script = ruleparse::parse_script(
        "::seg:: = [abcdefghijklmnopqrstuvwxyzñ']\n[1234] -> {14} / #(::seg::)+ _ \n[23] -> {4} / _ "
    )?;
    let fst = rulefst::compile_script(rulefst::unicode_symbol_table(),script.clone())?;
    for (i, rule) in enumerate(script) {
        println!("Rule {}: {:?}", i+1, rule);
    }
    let input = "ni1hao3".to_string();
    let e2e = rulefst::apply_fst_to_string(rulefst::unicode_symbol_table(), fst, input.clone()).unwrap();
    e2e.clone().draw("path_output", &DrawingConfig::default())?;
    let paths = rulefst::decode_paths_through_fst(rulefst::unicode_symbol_table(), e2e);
    if let Some((_, result)) = paths.first() {
        println!("{} -> {}", input, result);
    }
    else {
        println!("you get NOTHING. you LOSE. good DAY sir.");
    }
    //[MacroDef(("chars", Group([Disjunction([Group([Char('n')]), Group([Char('i')])]), Char('\n'), Class([Char('1'), Char('2'), Char('3'), Char('4')])])))]
    println!("Hello, world!");
    Ok(())
}
