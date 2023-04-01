use anyhow::Result;
use rustfst::prelude::*;
use std::collections::HashMap;


struct M2MFstAligner {
   // TODO: Fill in
   // ----- Training dataset metadata
   // 1. vector of alignments WFSTs, one for each training example
   // 2. total of type float, running sum for EM, is not reset
   // 3. partial counts of all unique inputs/outputs, running sum for EM, not reset
   //    - could be a hashtable of GraphemePhonemeAlignment structs
   // 4. unique egdes of type int, number of unique edges in 1.
   // 9. symbol table, maps Strings (symbols) to ints (labels), usually input/output as 2 symbols instead of 1
   // ----- Training metadata
   // 6. max phoneme subsequence
   // 7. max grapheme subsequence
   // ----- Maybe?
   // 5. training threshold
   // 8. max iterations of training
}

// Maybe have this struct for unique input/output transitions? Easier for comparison?
// Another option is to use this for partial counts?
#[derive(PartialEq, Eq, Hash)]
struct GPAlign(u32,u32);

impl M2MFstAligner {
   fn new() -> Self {
      // TODO: constructor for M2MFstAligner

      Self {
         // TODO: fill in with user parameters
      }
   }

   fn seq2fst(&mut self) {
      // TODO: converts grapheme-phoneme pair to FST
   }

   fn seqs2fsts(&mut self) {
      // TODO: given a list of grapheme-phoneme pairs, convert each one into a FST
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
                     trs.set_weight(i, self.partial_counts.get(&GPAlign(tr.ilabel, tr.olabel)).clone());
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