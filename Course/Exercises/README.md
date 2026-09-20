1. I have given some hints for the various exercises that include potentially
   useful theorems; these are the theorems that my own solution uses. Your
   solution may not use them if you take a different approach, and that's fine.
   However, you may need to look up some _different_ theorems in that case. Use
   the methods described in `L02_BasicProofs::USEFUL_THEOREMS` (and recapped in
   `L05_ComprehensiveRecap::FINDING_THEOREMS`) to find what you need.

2. A small tip when writing proofs: Lean's parser can get confused and make
   weird things happen if your proof is incomplete (i.e., you're currently
   working on it); this issue can also affect the infoview and make it show the
   wrong thing. The easiest way to prevent this is to put `_` or `sorry` where
   your current proof stops, so that Lean sees that the proof is technically
   "complete" and it won't make those errors.

    - `_` asks Lean to infer a type; it won't be able to, but it will give Lean
      a clear signal that the proof ends at that point

    - `sorry` will automatically prove the rest of the proof until you replace
      the `sorry` with the actual proof.

    - If your proof has multiple goals (e.g., as shown in the infoview), each
      one will need a `_` or `sorry`
