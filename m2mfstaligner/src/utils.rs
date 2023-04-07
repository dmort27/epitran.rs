fn split_on_graphemes(s: &str) -> Vec<String> {
   /*
      Given a string s in UTF-8 encoding, deconstruct s into a vector of its
      individual graphemes. This works well for languages whose written forms
      are composed of letters (e.g. English, Arabic, Spanish, German, etc). The
      result is a vector of individual letters in UTF-8 encoding.

      NOTE: This might not work as intended for languages whose written forms
      cannot be decomposed into letters (e.g. Chinese, Japanese kanji, etc) or
      into parts (e.g. Korean). Given a string of these languages, this function
      can split it into individual UTF-8 encoded characters, but they might not
      be what we want for G2P.
   */
   let bytes = s.as_bytes();
   let mut graphemes = Vec::new();
   let mut start = 0;
   let mut i = 0;
   while i <= bytes.len() {
      if s.is_char_boundary(i) {
         let mut temp = vec![0, i - start];
         temp.clone_from_slice(&bytes[start..i]);
         let grapheme = String::from_utf8(temp).unwrap();
         graphemes.push(grapheme);
         start = i;
      }
      i += 1;
   }

   graphemes
}