import Mathlib

namespace KKBinPacking.Shared

/-- Insertion of pieces "using a new bin only when necessary" (Lemma 3, p. 314; ALGORITHM 1,
Step 7, and ALGORITHM 2, Step 4, p. 316). `AnyFit P S Q` means: starting from the bins `P` and inserting the pieces of
`S` one at a time, in any order, each piece into any existing bin where it fits, and into a
new bin only when it fits in no existing bin, can end with the bins `Q`. -/
inductive AnyFit : Multiset (Multiset ℝ) → Multiset ℝ → Multiset (Multiset ℝ) → Prop
  /-- Nothing left to insert. -/
  | done (P : Multiset (Multiset ℝ)) : AnyFit P 0 P
  /-- Insert a piece `p` of `S` into an existing bin `b` where it fits. -/
  | intoBin (P : Multiset (Multiset ℝ)) (S : Multiset ℝ) (Q : Multiset (Multiset ℝ))
      (p : ℝ) (b : Multiset ℝ) :
      p ∈ S → b ∈ P → b.sum + p ≤ 1 →
      AnyFit ((P.erase b) + {p ::ₘ b}) (S.erase p) Q → AnyFit P S Q
  /-- Open a new bin for a piece `p` of `S` that fits in no existing bin. -/
  | newBin (P : Multiset (Multiset ℝ)) (S : Multiset ℝ) (Q : Multiset (Multiset ℝ)) (p : ℝ) :
      p ∈ S → (∀ b ∈ P, 1 < b.sum + p) →
      AnyFit (P + {{p}}) (S.erase p) Q → AnyFit P S Q

end KKBinPacking.Shared
