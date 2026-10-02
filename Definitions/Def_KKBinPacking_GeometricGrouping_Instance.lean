import Mathlib

namespace KKBinPacking.GeometricGrouping

/-- An instance of one-dimensional bin packing (p. 312): a finite multiset of piece sizes,
each strictly between `0` and `1`. -/
def IsInstance (I : Multiset ℝ) : Prop := ∀ x ∈ I, 0 < x ∧ x < 1

/-- `n(I)`, the number of pieces of `I` (p. 312). -/
def numPieces (I : Multiset ℝ) : ℕ := Multiset.card I

/-- `m(I)`, the number of distinct piece sizes of `I` (p. 312). -/
noncomputable def numSizes (I : Multiset ℝ) : ℕ := I.toFinset.card

/-- `SIZE(I)`, the sum of the sizes of all pieces of `I` (p. 312). -/
def SIZE (I : Multiset ℝ) : ℝ := I.sum

/-- `a(I)`, the smallest piece size of `I` (p. 312). Only meaningful for nonempty `I`; every
theorem using it assumes `I ≠ 0`. On the empty multiset it returns `1` (so `ln(1/a(I)) = 0`). -/
noncomputable def minSize (I : Multiset ℝ) : ℝ :=
  if h : I.toFinset.Nonempty then I.toFinset.min' h else 1

/-- A packing of `I`: a multiset of bins (each a multiset of piece sizes) whose union is
exactly `I` and in which every bin has total size at most `1`. Its cost is its number of
bins, `Multiset.card P`; empty bins are allowed and counted. -/
def IsPacking (I : Multiset ℝ) (P : Multiset (Multiset ℝ)) : Prop :=
  P.join = I ∧ ∀ b ∈ P, b.sum ≤ 1

/-- `OPT(I)`, the minimum number of bins in a packing of `I` (p. 312). For an instance the set
is nonempty (one piece per bin), so the infimum is attained. -/
noncomputable def OPT (I : Multiset ℝ) : ℕ :=
  sInf {B : ℕ | ∃ P : Multiset (Multiset ℝ), IsPacking I P ∧ Multiset.card P = B}

end KKBinPacking.GeometricGrouping
