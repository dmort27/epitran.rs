// use anyhow::Result;
use rustfst::prelude::*;
// Explicitly import VectorFst to avoid conflicts
use rustfst::fst_impls::VectorFst;
use std::collections::HashMap;
// use string_join::Join;


struct M2MFstAligner {
   // TODO: Fill in
   // ----- Training dataset metadata
   // 1. vector of alignments WFSTs, one for each training example
   lattices: Vec<VectorFst<LogWeight>>,
   // 2. total of type float, running sum for EM, is not reset
   total: LogWeight,
   // 3. partial counts of all unique inputs/outputs, running sum for EM, not reset
   partial_counts: HashMap<GPAlign, LogWeight>,
   //    - could be a hashtable of GraphemePhonemeAlignment structs
   // 4. unique egdes of type int, number of unique edges in 1.
   // num_unique: u32,
   // 9. symbol table, maps Strings (symbols) to ints (labels), usually input/output as 2 symbols instead of 1
   symbtbl: SymbolTable,
   grphm_eps: bool,
   phnm_eps: bool,
   restrict: bool,
   // ----- Training metadata
   // 6. max grapheme subsequence
   max_grphm_len: usize,
   // 7. max phoneme subsequence
   max_phnm_len: usize,
   // ----- Maybe?
   // 5. training threshold
   // 8. max iterations of training
   max_change: f32,
}

// Maybe have this struct for unique input/output transitions? Easier for comparison?
// Another option is to use this for partial counts?
#[derive(PartialEq, Eq, Hash)]
struct GPAlign(u32,u32);

impl M2MFstAligner {
   fn new(grphm_eps: bool, phnm_eps: bool, restrict: bool, max_grphm_len: usize, max_phnm_len: usize) -> Self {
      // TODO: constructor for M2MFstAligner

      Self {
         // TODO: fill in with user parameters
         lattices: Vec::new(),
         total: LogWeight::zero(),
         partial_counts: HashMap::new(),
         symbtbl: SymbolTable::new(),
         grphm_eps,
         phnm_eps,
         restrict,
         max_grphm_len,
         max_phnm_len,
         max_change: f32::NEG_INFINITY
      }
   }

   fn seqs2fsts(&mut self, data: &Vec<(Vec<String>, Vec<String>)>) -> Result<(), Box<dyn std::error::Error>> {
      // TODO: given a list of grapheme-phoneme pairs, convert each one into a FST
      for pair in data {
         let (grapheme_seq, phoneme_seq) = &pair;
         let mut fst = VectorFst::<LogWeight>::new();
         self.seq2fst(&mut fst, &grapheme_seq, &phoneme_seq)?;
         self.lattices.push(fst);
      }

      self.initialize(self.partial_counts.len() as f32)?;
      Ok(())
   }

   fn seq2fst(
      &mut self,
      fst: &mut VectorFst<LogWeight>, 
      grapheme_seq: &Vec<String>, 
      phoneme_seq: &Vec<String>
   ) -> Result<(), Box<dyn std::error::Error>> {   
      let mut istate;
      let mut ostate;
      for i in 0..(grapheme_seq.len() + 1) {
         for j in 0..(phoneme_seq.len() + 1) {
            istate = i * (phoneme_seq.len() + 1) + j;
   
            // Epsilon arcs for grapheme_seq
            if self.grphm_eps {
               for l in 1..(self.max_phnm_len + 1) {
                  if j + l <= phoneme_seq.len() {
                     let mut pseq = vec![String::new(); l];
                     pseq.clone_from_slice(&phoneme_seq[j..j+l]);
                     let symb = pseq.join("");
                     let olabel = if self.symbtbl.contains_symbol(&symb) {
                                    self.symbtbl.get_label(&symb).unwrap_or_else(|| {
                                        eprintln!("Warning: Symbol '{}' not found in symbol table, using epsilon", symb);
                                        0 // epsilon
                                    })
                                 } else {
                                    self.symbtbl.add_symbol(symb)
                                 };
                     ostate = i * (phoneme_seq.len() + 1) + (j + l);
                     if ostate + 1 > fst.num_states() {
                        fst.add_states(ostate - fst.num_states() + 1);
                     }
                     // symbtbl[0] is epsilon
                     fst.add_tr(istate as u32, Tr::new(0, olabel, 1.0, ostate as u32)).unwrap_or_else(|e| {
                         eprintln!("Warning: Could not add transition to FST: {}", e);
                     });
                     
                  }
               }
            }
   
            // Epsilon arcs for phoneme_seq
            if self.phnm_eps {
               for k in 1..(self.max_grphm_len + 1) {
                  if i + k <= grapheme_seq.len() {
                     let mut gseq = vec![String::new(); k];
                     gseq.clone_from_slice(&grapheme_seq[i..i+k]);
                     let symb = gseq.join("");
                     let ilabel = if self.symbtbl.contains_symbol(&symb) {
                                    self.symbtbl.get_label(&symb).unwrap_or_else(|| {
                                        eprintln!("Warning: Symbol '{}' not found in symbol table, using epsilon", symb);
                                        0 // epsilon
                                    })
                                 } else {
                                    self.symbtbl.add_symbol(symb)
                                 };
                     ostate = (i + k) * (phoneme_seq.len() + 1) + j;
                     if ostate + 1 > fst.num_states() {
                        fst.add_states(ostate - fst.num_states() + 1);
                     }
                     // symbtbl[0] is epsilon
                     fst.add_tr(istate as u32, Tr::new(ilabel, 0, 1.0, ostate as u32))?;
                  }
               }
            }
   
            // All the other arcs
            for k in 1..(self.max_grphm_len + 1) {
               for l in 1..(self.max_phnm_len + 1) {
                  // This says only 1-M and N-1 allowed, no M-N links!
                  if self.restrict && l > 1 && k > 1 {
                     continue
                  } else {
                     if (i + k) <= grapheme_seq.len() && (j + l) <= phoneme_seq.len() {
                        let mut gseq = vec![String::new(); k];
                        gseq.clone_from_slice(&grapheme_seq[i..i+k]);
                        let g_symb = gseq.join("");
                        let ilabel = if self.symbtbl.contains_symbol(&g_symb) {
                                       self.symbtbl.get_label(&g_symb).unwrap_or_else(|| {
                                           eprintln!("Warning: Symbol '{}' not found in symbol table, using epsilon", g_symb);
                                           0 // epsilon
                                       })
                                    } else {
                                       self.symbtbl.add_symbol(g_symb)
                                    };
   
                        let mut pseq = vec![String::new(); l];
                        pseq.clone_from_slice(&phoneme_seq[j..j+l]);
                        let p_symb = pseq.join("");
                        let olabel = if self.symbtbl.contains_symbol(&p_symb) {
                                       self.symbtbl.get_label(&p_symb).unwrap_or_else(|| {
                                           eprintln!("Warning: Symbol '{}' not found in symbol table, using epsilon", p_symb);
                                           0 // epsilon
                                       })
                                    } else {
                                       self.symbtbl.add_symbol(p_symb)
                                    };
   
                        ostate = (i + k) * (phoneme_seq.len() + 1) + (j + l);
                        if ostate + 1 > fst.num_states() {
                           fst.add_states(ostate - fst.num_states() + 1);
                        }
                        fst.add_tr(istate as u32, Tr::new(ilabel, olabel, 1.0, ostate as u32))?;
                     }
                  }
               }
            }
         }
      }
   
      fst.set_start(0)?;
      fst.set_final(((grapheme_seq.len() + 1) * (phoneme_seq.len() + 1) - 1) as u32, LogWeight::one())?;
   
      // Removes all states/transitions not connected to the final state
      connect(fst)?;
      // And add the remaining transitions into partial_counts
      for state_id in fst.states_iter() {
         let trs = fst.tr_iter_mut(state_id)?;
         for i in 0..trs.len() {
            let tr = trs.get(i).ok_or("Failed to get transition")?;
            if !self.partial_counts.contains_key(&GPAlign(tr.ilabel, tr.olabel)) {
               self.partial_counts.insert(GPAlign(tr.ilabel, tr.olabel), LogWeight::zero());
            }
         }
      }
      Ok(())
   }

   fn initialize(&mut self, num_unique_edges: f32) -> Result<(), Box<dyn std::error::Error>> {
      let weight = 1.0 / num_unique_edges;
      for lattice in self.lattices.iter_mut() {
         for state_id in lattice.states_iter() {
            let mut trs = lattice.tr_iter_mut(state_id)?;
            for i in 0..trs.len() {
               trs.set_weight(i, LogWeight::from(weight))?;
            }
         }
      }
      Ok(())
   }

   fn expectation(&mut self) -> Result<(), Box<dyn std::error::Error>> {
      // For all training alignment WFSTs in 1.
      for lattice in self.lattices.iter_mut() {
         //  alpha = shortest_distance(forward)
         let alpha = shortest_distance(lattice, false)?;
         //  beta = shortest_distance(backward)
         let beta = shortest_distance(lattice, true)?;

         //  for every transition
         let b0 = beta.get(0).ok_or("Failed to get beta[0]")?;
         for state_id in lattice.states_iter() {
            let trs = lattice.tr_iter_mut(state_id)?;
            for i in 0..trs.len() {
               let tr = trs.get(i).ok_or("Failed to get transition")?;
               let a = alpha.get(state_id as usize).ok_or("Failed to get alpha value")?;
               let b = beta.get(tr.nextstate as usize).ok_or("Failed to get beta value")?;
               let v = a.times(tr.weight)?
                        .times(b)?
                        .divide(b0, DivideType::DivideAny)?;
               let partial_count = self.partial_counts.get_mut(&GPAlign(tr.ilabel, tr.olabel))
                   .ok_or("Failed to get partial count")?;
               partial_count.plus_assign(v)?;
               self.total.plus_assign(v)?;
            }
         }
      }
      Ok(())
   }

   fn maximization(&mut self) -> Result<(), Box<dyn std::error::Error>> {
      // for every unique transition in partial_counts:
      for count in self.partial_counts.values_mut() {
         // partial_count[input,output] - total
         count.divide_assign(&self.total, DivideType::DivideAny)?;
      }
      Ok(())
   }

   fn reset_tr_weights(&mut self) -> Result<(), Box<dyn std::error::Error>> {
      for lattice in self.lattices.iter_mut() {
         for state_id in lattice.states_iter() {
            let mut trs = lattice.tr_iter_mut(state_id)?;
            for i in 0..trs.len() {
               // https://docs.rs/rustfst/latest/rustfst/trs_iter_mut/struct.TrsIterMut.html
               let tr = trs.get(i).ok_or("Failed to get transition")?;
               let partial_count = self.partial_counts.get(&GPAlign(tr.ilabel, tr.olabel))
                   .ok_or("Failed to get partial count for transition")?;
               if (tr.weight.value() - partial_count.value()).abs() > self.max_change {
                  self.max_change = (tr.weight.value() - partial_count.value()).abs();
               }
               trs.set_weight(i, LogWeight::new(*partial_count.value()))?;
            }
         }
      }
      Ok(())
   }

   fn expectation_maximization(&mut self, max_iter: u32, threshold: f32) -> Result<(), Box<dyn std::error::Error>> {
      /*
         Perform the expectation-maximization algorithm for a predetermined
         number of iterations or until the maximum change in a transition
         weight is less than a provided threshold.
       */
      let mut iter = 0;

      while iter < max_iter && !self.check_convergence(threshold) {
         self.expectation()?;
         self.maximization()?;
         self.reset_tr_weights()?;
         iter += 1;
      }
      Ok(())
   }

   fn check_convergence(&self, threshold: f32) -> bool {
      /*
         Returns whether the maximum change in transition weights is less than
         a predefined threshold.
       */
      self.max_change < threshold
   }

}

#[cfg(test)]
mod tests {
   use super::*;
   // No need to re-import these as they're already imported in the parent module
   // use rustfst::prelude::*;
   // use std::collections::HashMap;


   #[test]
   fn test_seq2fst() {
      // Example from Phonetisaurus paper Fig. 3, hand-verified
      // Create an empty WFST
      let mut gold = VectorFst::<LogWeight>::new();
      let mut st = SymbolTable::new();

      // Add some states
      let s0 = gold.add_state();
      let s1 = gold.add_state();
      let s2 = gold.add_state();
      let s3 = gold.add_state();
      let s4 = gold.add_state();
      let s5 = gold.add_state();
      let s6 = gold.add_state();
      let s7 = gold.add_state();
      let s8 = gold.add_state();
      let s9 = gold.add_state();
      let s10 = gold.add_state();
      let s11 = gold.add_state();

      // Set s0 as the start state
      gold.set_start(s0).expect("Test assertion failed");

      // Add a transition from s0
      gold.add_tr(s0, Tr::new(st.add_symbol("r"), 0, 1.0/27.0, s1)).expect("Test assertion failed");
      gold.add_tr(s0, Tr::new(st.add_symbol("ri"), 0, 1.0/27.0, s2)).expect("Test assertion failed");
      gold.add_tr(s0, Tr::new(st.get_label("r").expect("Test assertion failed"), st.get_label("r").expect("Test assertion failed"), 1.0/27.0, s3)).expect("Test assertion failed");
      gold.add_tr(s0, Tr::new(st.get_label("ri").expect("Test assertion failed"), st.get_label("r").expect("Test assertion failed"), 1.0/27.0, s4)).expect("Test assertion failed");

      // Add a transition from s1 
      gold.add_tr(s1, Tr::new(st.add_symbol("i"), 0, 1.0/27.0, s2)).expect("Test assertion failed");
      gold.add_tr(s1, Tr::new(st.get_label("i").expect("Test assertion failed"), st.get_label("r").expect("Test assertion failed"), 1.0/27.0, s4)).expect("Test assertion failed");
      gold.add_tr(s1, Tr::new(st.add_symbol("ig"), st.get_label("r").expect("Test assertion failed"), 1.0/27.0, s6)).expect("Test assertion failed");

      // Add a transition from s2
      gold.add_tr(s2, Tr::new(st.add_symbol("g"), st.get_label("r").expect("Test assertion failed"), 1.0/27.0, s6)).expect("Test assertion failed");

      gold.add_tr(s3, Tr::new(st.get_label("i").expect("Test assertion failed"), 0, 1.0/27.0, s4)).expect("Test assertion failed");
      gold.add_tr(s3, Tr::new(st.get_label("i").expect("Test assertion failed"), st.add_symbol("ay"), 1.0/27.0, s5)).expect("Test assertion failed");
      gold.add_tr(s3, Tr::new(st.get_label("ig").expect("Test assertion failed"), 0, 1.0/27.0, s6)).expect("Test assertion failed");
      gold.add_tr(s3, Tr::new(st.get_label("ig").expect("Test assertion failed"), st.get_label("ay").expect("Test assertion failed"), 1.0/27.0, s7)).expect("Test assertion failed");

      gold.add_tr(s4, Tr::new(st.get_label("g").expect("Test assertion failed"), 0, 1.0/27.0, s6)).expect("Test assertion failed");
      gold.add_tr(s4, Tr::new(st.get_label("g").expect("Test assertion failed"), st.get_label("ay").expect("Test assertion failed"), 1.0/27.0, s7)).expect("Test assertion failed");
      gold.add_tr(s4, Tr::new(st.add_symbol("gh"), st.get_label("ay").expect("Test assertion failed"), 1.0/27.0, s9)).expect("Test assertion failed");

      gold.add_tr(s5, Tr::new(st.get_label("g").expect("Test assertion failed"), 0, 1.0/27.0, s7)).expect("Test assertion failed");
      gold.add_tr(s5, Tr::new(st.get_label("g").expect("Test assertion failed"), st.add_symbol("t"), 1.0/27.0, s8)).expect("Test assertion failed");
      gold.add_tr(s5, Tr::new(st.get_label("gh").expect("Test assertion failed"), 0, 1.0/27.0, s9)).expect("Test assertion failed");
      gold.add_tr(s5, Tr::new(st.get_label("gh").expect("Test assertion failed"), st.get_label("t").expect("Test assertion failed"), 1.0/27.0, s10)).expect("Test assertion failed");

      gold.add_tr(s6, Tr::new(st.add_symbol("h"), st.get_label("ay").expect("Test assertion failed"), 1.0/27.0, s9)).expect("Test assertion failed");

      gold.add_tr(s7, Tr::new(st.get_label("h").expect("Test assertion failed"), 0, 1.0/27.0, s9)).expect("Test assertion failed");
      gold.add_tr(s7, Tr::new(st.get_label("h").expect("Test assertion failed"), st.get_label("t").expect("Test assertion failed"), 1.0/27.0, s10)).expect("Test assertion failed");
      gold.add_tr(s7, Tr::new(st.add_symbol("ht"), st.get_label("t").expect("Test assertion failed"), 1.0/27.0, s11)).expect("Test assertion failed");

      gold.add_tr(s8, Tr::new(st.get_label("h").expect("Test assertion failed"), 0, 1.0/27.0, s10)).expect("Test assertion failed");
      gold.add_tr(s8, Tr::new(st.get_label("ht").expect("Test assertion failed"), 0, 1.0/27.0, s11)).expect("Test assertion failed");


      gold.add_tr(s9, Tr::new(st.get_label("t").expect("Test assertion failed"), st.get_label("t").expect("Test assertion failed"), 1.0/27.0, s11)).expect("Test assertion failed");

      gold.add_tr(s10, Tr::new(st.get_label("t").expect("Test assertion failed"), 0, 1.0/27.0, s11)).expect("Test assertion failed");

      gold.set_final(s11, 0.0).expect("Test assertion failed");


      // Make a M2MFstAligner object, initialize it from scratch, and align
      // R I G H T -> R AY T
      let mut aligner = M2MFstAligner::new(false, true, true, 2, 1);
      let mut data = Vec::new();
      let grphm = vec![String::from("r"), String::from("i"), String::from("g"), String::from("h"), String::from("t")];
      let phnm = vec![String::from("r"), String::from("ay"), String::from("t")];
      data.push((grphm, phnm));
      aligner.seqs2fsts(&data);

      // Compare gold to actual
      let fst = aligner.lattices.get(0).expect("Test assertion failed");
      let symbtbl = aligner.symbtbl;
      // for state_id in fst.states_iter() {
      //    let trs = fst.get_trs(state_id).expect("Test assertion failed");
      //    for tr in trs.iter() {
      //       println!("ISTATE: {}, ilabel: {}, olabel: {}, weight: {}, OSTATE: {}", 
      //                state_id, 
      //                symbtbl.get_symbol(tr.ilabel).expect("Test assertion failed"), 
      //                symbtbl.get_symbol(tr.olabel).expect("Test assertion failed"),
      //                tr.weight,
      //                tr.nextstate
      //             )
      //    }
      // }
      // assert!(gold.eq(fst));
      assert!(gold.num_states() == fst.num_states());
      for state_id in gold.states_iter() {
         let gold_trs = gold.get_trs(state_id).expect("Test assertion failed");
         let trs = fst.get_trs(state_id).expect("Test assertion failed");
         for it in gold_trs.iter().zip(trs.iter()) {
            let (gold_tr, tr) = it;
            assert!(st.get_symbol(gold_tr.ilabel) == symbtbl.get_symbol(tr.ilabel));
            assert!(st.get_symbol(gold_tr.olabel) == symbtbl.get_symbol(tr.olabel));
            assert!(gold_tr.weight.value() == tr.weight.value());
         }
      }
   }

   #[test]
   fn test_expectation() {
      let mut gold_partial_counts = HashMap::new();
      gold_partial_counts.insert(GPAlign(0,1), LogWeight::new(1.4337094291003556));
      gold_partial_counts.insert(GPAlign(0,2), LogWeight::new(3.3586238126029357));
      gold_partial_counts.insert(GPAlign(0,3), LogWeight::new(0.597375770952433));
      gold_partial_counts.insert(GPAlign(0,4), LogWeight::new(1.73420607818958));
      gold_partial_counts.insert(GPAlign(1,2), LogWeight::new(3.3956608496399725));
      gold_partial_counts.insert(GPAlign(1,4), LogWeight::new(1.771243115226617));
      gold_partial_counts.insert(GPAlign(1,6), LogWeight::new(3.3586238126029357));
      gold_partial_counts.insert(GPAlign(2,6), LogWeight::new(2.6838236925969503));
      gold_partial_counts.insert(GPAlign(3,4), LogWeight::new(1.771243115226617));
      gold_partial_counts.insert(GPAlign(3,5), LogWeight::new(1.4284190162117816));
      gold_partial_counts.insert(GPAlign(3,6), LogWeight::new(3.3586238126029357));
      gold_partial_counts.insert(GPAlign(3,7), LogWeight::new(2.247512807785858));
      gold_partial_counts.insert(GPAlign(4,6), LogWeight::new(2.2845498448228954));
      gold_partial_counts.insert(GPAlign(4,7), LogWeight::new(1.1734388400058182));
      gold_partial_counts.insert(GPAlign(4,9), LogWeight::new(2.247512807785858));
      gold_partial_counts.insert(GPAlign(5,7), LogWeight::new(2.2845498448228954));
      gold_partial_counts.insert(GPAlign(5,8), LogWeight::new(2.6838236925969503));
      gold_partial_counts.insert(GPAlign(5,9), LogWeight::new(3.3586238126029357));
      gold_partial_counts.insert(GPAlign(5,10), LogWeight::new(3.3586238126029357));
      gold_partial_counts.insert(GPAlign(6,9), LogWeight::new(1.4284190162117816));
      gold_partial_counts.insert(GPAlign(7,9), LogWeight::new(1.771243115226617));
      gold_partial_counts.insert(GPAlign(7,10), LogWeight::new(1.771243115226617));
      gold_partial_counts.insert(GPAlign(7,11), LogWeight::new(1.73420607818958));
      gold_partial_counts.insert(GPAlign(8,10), LogWeight::new(3.3956608496399725));
      gold_partial_counts.insert(GPAlign(8,11), LogWeight::new(3.3586238126029357));
      gold_partial_counts.insert(GPAlign(9,11), LogWeight::new(0.597375770952433));
      gold_partial_counts.insert(GPAlign(10,11), LogWeight::new(1.4337094291003556));


      let mut aligner = M2MFstAligner::new(false, true, true, 2, 1);
      let mut data = Vec::new();
      let grphm = vec![String::from("r"), String::from("i"), String::from("g"), String::from("h"), String::from("t")];
      let phnm = vec![String::from("r"), String::from("ay"), String::from("t")];
      data.push((grphm, phnm));
      aligner.seqs2fsts(&data);
      aligner.expectation();

      assert!((-1.4414682 - aligner.total.value()).abs() < 0.0001);
      let partial_counts = aligner.partial_counts;
      assert!(gold_partial_counts.len() == partial_counts.len());
      for (key, val) in partial_counts.iter() {
         assert!(gold_partial_counts.contains_key(key));
         assert!((gold_partial_counts.get(key).expect("Test assertion failed").value() - val.value()).abs() < 0.0001);
      }
   }

   #[test]
   fn test_maximization() {
      let mut gold_partial_counts = HashMap::new();
      gold_partial_counts.insert(GPAlign(0,1), LogWeight::new(2.875177684923876));
      gold_partial_counts.insert(GPAlign(0,2), LogWeight::new(4.800092068426457));
      gold_partial_counts.insert(GPAlign(0,3), LogWeight::new(2.0388440267759536));
      gold_partial_counts.insert(GPAlign(0,4), LogWeight::new(3.1756743340131006));
      gold_partial_counts.insert(GPAlign(1,2), LogWeight::new(4.837129105463493));
      gold_partial_counts.insert(GPAlign(1,4), LogWeight::new(3.212711371050138));
      gold_partial_counts.insert(GPAlign(1,6), LogWeight::new(4.800092068426457));
      gold_partial_counts.insert(GPAlign(2,6), LogWeight::new(4.125191948420471));
      gold_partial_counts.insert(GPAlign(3,4), LogWeight::new(3.212711371050138));
      gold_partial_counts.insert(GPAlign(3,5), LogWeight::new(2.869887272035302));
      gold_partial_counts.insert(GPAlign(3,6), LogWeight::new(4.800092068426457));
      gold_partial_counts.insert(GPAlign(3,7), LogWeight::new(3.6889810636093787));
      gold_partial_counts.insert(GPAlign(4,6), LogWeight::new(3.726018100646416));
      gold_partial_counts.insert(GPAlign(4,7), LogWeight::new(2.614907095829339));
      gold_partial_counts.insert(GPAlign(4,9), LogWeight::new(3.6889810636093787));
      gold_partial_counts.insert(GPAlign(5,7), LogWeight::new(3.726018100646416));
      gold_partial_counts.insert(GPAlign(5,8), LogWeight::new(4.125191948420471));
      gold_partial_counts.insert(GPAlign(5,9), LogWeight::new(4.800092068426457));
      gold_partial_counts.insert(GPAlign(5,10), LogWeight::new(4.800092068426457));
      gold_partial_counts.insert(GPAlign(6,9), LogWeight::new(2.869887272035302));
      gold_partial_counts.insert(GPAlign(7,9), LogWeight::new(3.212711371050138));
      gold_partial_counts.insert(GPAlign(7,10), LogWeight::new(3.212711371050138));
      gold_partial_counts.insert(GPAlign(7,11), LogWeight::new(3.1756743340131006));
      gold_partial_counts.insert(GPAlign(8,10), LogWeight::new(4.837129105463493));
      gold_partial_counts.insert(GPAlign(8,11), LogWeight::new(4.800092068426457));
      gold_partial_counts.insert(GPAlign(9,11), LogWeight::new(2.0388440267759536));
      gold_partial_counts.insert(GPAlign(10,11), LogWeight::new(2.875177684923876));

      let mut aligner = M2MFstAligner::new(false, true, true, 2, 1);
      let mut data = Vec::new();
      let grphm = vec![String::from("r"), String::from("i"), String::from("g"), String::from("h"), String::from("t")];
      let phnm = vec![String::from("r"), String::from("ay"), String::from("t")];
      data.push((grphm, phnm));
      aligner.seqs2fsts(&data);
      aligner.expectation();
      aligner.maximization();

      let partial_counts = aligner.partial_counts;
      assert!(gold_partial_counts.len() == partial_counts.len());
      for (key, val) in partial_counts.iter() {
         assert!(gold_partial_counts.contains_key(key));
         assert!((gold_partial_counts.get(key).expect("Test assertion failed").value() - val.value()).abs() < 0.0001);
      }
   }

   #[test]
   fn test_reset_weights() {
      let mut gold = VectorFst::<LogWeight>::new();
      let mut st = SymbolTable::new();

      // Add some states
      let s0 = gold.add_state();
      let s1 = gold.add_state();
      let s2 = gold.add_state();
      let s3 = gold.add_state();
      let s4 = gold.add_state();
      let s5 = gold.add_state();
      let s6 = gold.add_state();
      let s7 = gold.add_state();
      let s8 = gold.add_state();
      let s9 = gold.add_state();
      let s10 = gold.add_state();
      let s11 = gold.add_state();

      // Set s0 as the start state
      gold.set_start(s0).expect("Test assertion failed");

      // Add a transition from s0
      gold.add_tr(s0, Tr::new(st.add_symbol("r"), 0, 2.875177684923876, s1)).expect("Test assertion failed");
      gold.add_tr(s0, Tr::new(st.add_symbol("ri"), 0, 4.800092068426457, s2)).expect("Test assertion failed");
      gold.add_tr(s0, Tr::new(st.get_label("r").expect("Test assertion failed"), st.get_label("r").expect("Test assertion failed"), 2.0388440267759536, s3)).expect("Test assertion failed");
      gold.add_tr(s0, Tr::new(st.get_label("ri").expect("Test assertion failed"), st.get_label("r").expect("Test assertion failed"), 3.1756743340131006, s4)).expect("Test assertion failed");

      // Add a transition from s1 
      gold.add_tr(s1, Tr::new(st.add_symbol("i"), 0, 4.837129105463493, s2)).expect("Test assertion failed");
      gold.add_tr(s1, Tr::new(st.get_label("i").expect("Test assertion failed"), st.get_label("r").expect("Test assertion failed"), 3.212711371050138, s4)).expect("Test assertion failed");
      gold.add_tr(s1, Tr::new(st.add_symbol("ig"), st.get_label("r").expect("Test assertion failed"), 4.800092068426457, s6)).expect("Test assertion failed");

      // Add a transition from s2
      gold.add_tr(s2, Tr::new(st.add_symbol("g"), st.get_label("r").expect("Test assertion failed"), 4.125191948420471, s6)).expect("Test assertion failed");

      gold.add_tr(s3, Tr::new(st.get_label("i").expect("Test assertion failed"), 0, 3.212711371050138, s4)).expect("Test assertion failed");
      gold.add_tr(s3, Tr::new(st.get_label("i").expect("Test assertion failed"), st.add_symbol("ay"), 2.869887272035302, s5)).expect("Test assertion failed");
      gold.add_tr(s3, Tr::new(st.get_label("ig").expect("Test assertion failed"), 0, 4.800092068426457, s6)).expect("Test assertion failed");
      gold.add_tr(s3, Tr::new(st.get_label("ig").expect("Test assertion failed"), st.get_label("ay").expect("Test assertion failed"), 3.6889810636093787, s7)).expect("Test assertion failed");

      gold.add_tr(s4, Tr::new(st.get_label("g").expect("Test assertion failed"), 0, 3.726018100646416, s6)).expect("Test assertion failed");
      gold.add_tr(s4, Tr::new(st.get_label("g").expect("Test assertion failed"), st.get_label("ay").expect("Test assertion failed"), 2.614907095829339, s7)).expect("Test assertion failed");
      gold.add_tr(s4, Tr::new(st.add_symbol("gh"), st.get_label("ay").expect("Test assertion failed"), 3.6889810636093787, s9)).expect("Test assertion failed");

      gold.add_tr(s5, Tr::new(st.get_label("g").expect("Test assertion failed"), 0, 3.726018100646416, s7)).expect("Test assertion failed");
      gold.add_tr(s5, Tr::new(st.get_label("g").expect("Test assertion failed"), st.add_symbol("t"), 4.125191948420471, s8)).expect("Test assertion failed");
      gold.add_tr(s5, Tr::new(st.get_label("gh").expect("Test assertion failed"), 0, 4.800092068426457, s9)).expect("Test assertion failed");
      gold.add_tr(s5, Tr::new(st.get_label("gh").expect("Test assertion failed"), st.get_label("t").expect("Test assertion failed"), 4.800092068426457, s10)).expect("Test assertion failed");

      gold.add_tr(s6, Tr::new(st.add_symbol("h"), st.get_label("ay").expect("Test assertion failed"), 2.869887272035302, s9)).expect("Test assertion failed");

      gold.add_tr(s7, Tr::new(st.get_label("h").expect("Test assertion failed"), 0, 3.212711371050138, s9)).expect("Test assertion failed");
      gold.add_tr(s7, Tr::new(st.get_label("h").expect("Test assertion failed"), st.get_label("t").expect("Test assertion failed"), 3.212711371050138, s10)).expect("Test assertion failed");
      gold.add_tr(s7, Tr::new(st.add_symbol("ht"), st.get_label("t").expect("Test assertion failed"), 3.1756743340131006, s11)).expect("Test assertion failed");

      gold.add_tr(s8, Tr::new(st.get_label("h").expect("Test assertion failed"), 0, 4.837129105463493, s10)).expect("Test assertion failed");
      gold.add_tr(s8, Tr::new(st.get_label("ht").expect("Test assertion failed"), 0, 4.800092068426457, s11)).expect("Test assertion failed");


      gold.add_tr(s9, Tr::new(st.get_label("t").expect("Test assertion failed"), st.get_label("t").expect("Test assertion failed"), 2.0388440267759536, s11)).expect("Test assertion failed");

      gold.add_tr(s10, Tr::new(st.get_label("t").expect("Test assertion failed"), 0, 2.875177684923876, s11)).expect("Test assertion failed");

      gold.set_final(s11, 0.0).expect("Test assertion failed");

      let mut aligner = M2MFstAligner::new(false, true, true, 2, 1);
      let mut data = Vec::new();
      let grphm = vec![String::from("r"), String::from("i"), String::from("g"), String::from("h"), String::from("t")];
      let phnm = vec![String::from("r"), String::from("ay"), String::from("t")];
      data.push((grphm, phnm));
      aligner.seqs2fsts(&data);

      aligner.expectation();
      aligner.maximization();
      aligner.reset_tr_weights();

      let fst = aligner.lattices.get(0).expect("Test assertion failed");
      let symbtbl = aligner.symbtbl;
      for state_id in gold.states_iter() {
         let gold_trs = gold.get_trs(state_id).expect("Test assertion failed");
         let trs = fst.get_trs(state_id).expect("Test assertion failed");
         for it in gold_trs.iter().zip(trs.iter()) {
            let (gold_tr, tr) = it;
            assert!(st.get_symbol(gold_tr.ilabel) == symbtbl.get_symbol(tr.ilabel));
            assert!(st.get_symbol(gold_tr.olabel) == symbtbl.get_symbol(tr.olabel));
            assert!(gold_tr.weight.value() == tr.weight.value());
         }
      }
   }

}