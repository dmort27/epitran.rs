use std::fs::File;
use std::io;
use std::path::Path;
use unicode_segmentation::UnicodeSegmentation;

fn read_training_file(filepath: &str) 
   -> Result<Vec<(Vec<String>, Vec<String>)>, &'static str>
{
   let path = Path::new(&filepath);
   let display = path.display();

   let file = match File::open(&path) {
      Err(why) => panic!("Could not open {}: {}", display, why),
      Ok(file) => file,
   };
   let mut rdr = csv::ReaderBuilder::new()
      .has_headers(false)
      .from_reader(file);

   let mut data = Vec::new();
   for result in rdr.records() {
      let record = result.unwrap_or_default();
      
      let graphemes: Vec<String> = String::from(&record[0])
                                    .graphemes(true)
                                    .map(|s| s.to_string())
                                    .collect();
      let phonemes: Vec<String> = String::from(&record[1])
                                    .split_whitespace()
                                    .map(|s| s.to_string())
                                    .collect();
      data.push((graphemes, phonemes));
   }

   Ok(data)
}