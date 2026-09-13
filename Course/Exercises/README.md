A small tip when writing proofs, especially when there is code after the proof
you are writing: Lean's parser can get confused and make weird things happen
because it thinks the code below is part of the current proof. The easiest way
to prevent this is to put `_` or `sorry` where your current proof stops, so that
Lean sees that's the end of the current proof and the code below it is separate.

- `_` asks Lean to infer a type; it won't be able to, but it will give Lean a
  clear signal that the proof ends at that point

- `sorry` will automatically prove the rest of the proof until you replace the
  `sorry` with the actual proof.

- If your proof has multiple goals, each one will need a `_` or `sorry`
