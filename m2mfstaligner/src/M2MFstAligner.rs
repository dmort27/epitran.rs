use anyhow::Result;
use rustfst::prelude::*;
use std::collections::HashMap;
use string_join::Join;


struct M2MFstAligner {
   // TODO: Fill in
   // ----- Training dataset metadata
   // 1. vector of alignments WFSTs, one for each training example
   lattices: Vec<LogWeight>,
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
}

// Maybe have this struct for unique input/output transitions? Easier for comparison?
// Another option is to use this for partial counts?
#[derive(PartialEq, Eq, Hash)]
struct GPAlign(u32,u32);

impl M2MFstAligner {
   fn new(max_grphm_len: usize, max_phnm_len: usize) -> Self {
      // TODO: constructor for M2MFstAligner

      Self {
         // TODO: fill in with user parameters
         lattices: Vec::new(),
         total: LogWeight::zero(),
         partial_counts: HashMap::new(),
         symbtbl: SymbolTable::new(),
         max_grphm_len,
         max_phnm_len,
      }
   }

   fn seqs2fsts(&mut self, data: &Vec<(Vec<String>, Vec<String>)>) {
      // TODO: given a list of grapheme-phoneme pairs, convert each one into a FST
      for pair in data {
         let (grapheme_seq, phoneme_seq) = &pair;
         let mut fst = VectorFst<LogWeight>::new();
         self.seq2fst(&mut fst, &grapheme_seq, &phoneme_seq);
         self.lattices.push(fst);
      }

      self.initialize(self.partial_counts.len() as f32);
   }

   fn seq2fst(
      &mut self, 
      fst: &mut VectorFst<LogWeight>, 
      grapheme_seq: &Vec<String>, 
      phoneme_seq: &Vec<String>
   ) {
      // TODO: converts grapheme-phoneme pair to FST
      // let mut fst = VectorFst<LogWeight>::new();
      // let s0 = fst.add_state();

      let mut istate = 0;
      let mut ostate = 0;
      for i in 0..grapheme_seq.len() {
         for j in 0..phoneme_seq.len() {
            istate = i * (phoneme_seq.len() + 1) + j;

            // Epsilon arcs for grapheme_seq
            if self.grphm_eps {
               for l in 1..(self.max_phnm_len + 1) {
                  if j + l <= phoneme_seq.len() {
                     let mut pseq = vec![String::new(); l];
                     pseq.clone_from_slice(&phoneme_seq[j..j+l]);
                     let symb = pseq.join("");
                     let olabel = if self.symbtbl.contains_symbol(symb) {
                                    self.symbtbl.get_label(symb).unwrap()
                                  } else {
                                    self.symbtbl.add_symbol(symb)
                                  };
                     ostate = i * (phoneme_seq.len() + 1) + (j + 1);
                     if ostate + 1 > fst.num_states() {
                        fst.add_states(ostate - fst.num_states() + 1);
                     }
                     // symbtbl[0] is epsilon
                     fst.add_tr(istate as u32, Tr::new(0, olabel, 1.0, ostate as u32));
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
                     let ilabel = if self.symbtbl.contains_symbol(symb) {
                                    self.symbtbl.get_label(symb).unwrap()
                                  } else {
                                    self.symbtbl.add_symbol(symb)
                                  };
                     ostate = (i + k) * (phoneme_seq.len() + 1) + j;
                     if ostate + 1 > fst.num_states() {
                        fst.add_states(ostate - fst.num_states() + 1);
                     }
                     // symbtbl[0] is epsilon
                     fst.add_tr(istate as u32, Tr::new(ilabel, 0, 1.0, ostate as u32));
                  }
               }
            }

            // All the other arcs
            for k in (1..(self.max_grphm_len + 1)) {
               for l in (1..(self.max_phnm_len + 1)) {
                  // This says only 1-M and N-1 allowed, no M-N links!
                  if self.restrict && l > 1 && k > 1 {
                     continue
                  } else {
                     if (i + k) <= grapheme_seq.len() && (j + l) <= phoneme_seq.len() {
                        let mut gseq = vec![String::new(); l];
                        gseq.clone_from_slice(&grapheme_seq[i..i+k]);
                        let g_symb = gseq.join("");
                        let ilabel = if self.symbtbl.contains_symbol(g_symb) {
                                       self.symbtbl.get_label(g_symb).unwrap()
                                     } else {
                                       self.symbtbl.add_symbol(g_symb)
                                     };

                        let mut pseq = vec![String::new(); l];
                        pseq.clone_from_slice(&phoneme_seq[j..j+l]);
                        let p_symb = pseq.join("");
                        let olabel = if self.symbtbl.contains_symbol(p_symb) {
                                       self.symbtbl.get_label(p_symb).unwrap()
                                     } else {
                                       self.symbtbl.add_symbol(p_symb)
                                     };

                        ostate = (i + k) * (phoneme_seq.len() + 1) + (j + 1);
                        if ostate + 1 > fst.num_states() {
                           fst.add_states(ostate - fst.num_states() + 1);
                        }
                        fst.add_tr(istate as u32, Tr::new(ilabel, olabel, 1.0, ostate as u32));
                     }
                  }
               }
            }
         }
      }

      fst.set_start(0);
      fst.set_final(((grapheme_seq.len() + 1) * (phoneme_seq.len() + 1) - 1) as u32, LogWeight::one());

      // Removes all states/transitions not connected to the final state
      connect(&mut fst)?;
   }

   fn initialize(&mut self, num_unique_edges: f32) {
      let weight = 1.0 / num_unique_edges;
      for lattice in self.lattices {
         for state_id in lattice.states_iter() {
            let trs = lattice.tr_iter_mut(state_id)?;
            for i in 0..trs.len() {
               trs.set_weight(i, LogWeight::from(weight));
            }
         }
      }
   }

   fn expectation(&mut self) { // return necessary?
      // For all training alignment WFSTs in 1.
      for lattice in self.lattices {
         //  alpha = shortest_distance(forward)
         let alpha = shortest_distance(&lattice, false)?;
         //  beta = shortest_distance(backward)
         let beta = shortest_distance(&lattice, true)?;
         //  for every transition

         let b0_opt = beta.get(0);
         if let Some(b0) = b0_opt {
            for state_id in lattice.states_iter() {
               let trs = lattice.tr_iter_mut(state_id)?;
               for i in 0..trs.len() {
                  let tr_opt = trs.get(i);
                  match tr_opt {
                     Some(tr) => {
                        let alpha_opt = alpha.get(state_id as usize);
                        if let Some(a) = alpha_opt {
                           let beta_opt = beta.get(tr.nextstate as usize);
                           if let Some(b) = beta_opt {
                              let v = a.times(tr.weight)?.times(b)?.divide(b0, DivideType::DivideAny)?;
                              if let Some(partial_count) = self.partial_counts.get_mut(&GPAlign(tr.ilabel, tr.olabel)) {
                                 partial_count.plus_assign(v)?;
                              }
                              // self.partial_count[GPAlign(tr.ilabel, tr.olabel)].plus_assign(v)?;
                              self.total.plus_assign(v)?;

                              //   v = alpha[input] log* transition weight log* beta[output] log/ beta[start]
                              // let v = alpha[state_id as usize].plus(tr.weight)?.plus(beta[tr.nextstate])?.divide(beta[0])?;
                              //   partial_count[input,output] log+ v
                              // self.partial_count[GPAlign(tr.ilabel, tr.olabel)].plus_assign(v)?;
                              //   total log+ v
                              // self.total.plus_assign(v)?;
                           }
                        }
                     },
                     _ => continue, // TODO: shouldn't ever fail, but if it does, maybe throw an error?
                  }
               }
            }
         } // TODO: shouldn't ever hit else, but if it does, maybe throw an error?
      }
   }

   fn maximization(&mut self) { // return necessary? 
      // for every unique transition in partial_counts:
      for count in self.partial_counts.values_mut() {
         // partial_count[input,output] - total
         count.divide_assign(&self.total, DivideType::DivideAny)?;
      }
   }

   fn reset_tr_weights(&mut self) { // have this return the max change in weight?
      for lattice in self.lattices {
         for state_id in lattice.states_iter() {
            let trs = lattice.tr_iter_mut(state_id)?;
            for i in 0..trs.len() {
               // https://docs.rs/rustfst/latest/rustfst/trs_iter_mut/struct.TrsIterMut.html
               let tr_opt = trs.get(i);
               match tr_opt {
                  Some(tr) => {
                     // trs.set_weight(i, self.partial_counts.get(&GPAlign(tr.ilabel, tr.olabel)).clone());
                     if let Some(partial_count) = self.partial_counts.get_mut(&GPAlign(tr.ilabel, tr.olabel)) {
                        trs.set_weight(i, partial_count.clone());
                     }
                  },
                  _ => continue, // TODO: shouldn't ever fail, but if it does, maybe throw an error?
               }
            }
         }
      }
   }

   fn EM(&mut self, max_iter: u32, threshold: f32) { // return necessary?
      // while iter < max_iters or change(prev, next) < threshold
      //    expectation()
      //    maximization()
      //    reset_tr_weights()
      //    threshold check: (1) max change in weight < theshold
      //                     (2) average change in weights < threshold
      let mut iter = 0;

      while iter < max_iter && self.check_convergence(threshold) {
         self.expectation();
         self.maximization();
         // reset weights of lattices with partial_counts
         self.reset_tr_weights();
         iter += 1;
      }
   }

   fn check_convergence(&self, threshold: f32) -> bool {
      // TODO: what should the convergence threshold check be?
      //       Option 1: max change in transition weight < threshold
      //       Option 2: average change in weights < threshold
      // NOTE: intuition max would probably be more stable, so stick with this
   }

}