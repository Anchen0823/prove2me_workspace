import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

/-!
# Binary strings with no adjacent ones

A binary string of length `n` is represented, in the most Mathlib-native way, as a
function `f : Fin n → Bool`. A string has *no adjacent ones* when no two consecutive
positions are both `true`. The same family is equivalently the family of finite
subsets of `Fin n` with no two consecutive elements (the independent sets of a path
graph).

This file provides:

* `NoAdjacentOnes` and `Finset.noAdjacent` — the two formulations of the property;
* `boolFinsetEquiv` — the canonical equivalence `(Fin n → Bool) ≃ Finset (Fin n)`;
* `GapMono` — strictly monotone position tuples whose successive entries differ by at
  least two, the carrier used to count strings with exactly `k` ones;
* `noAdjacentStrings`, `noAdjacentStringsCard`, `noAdjacentFinset`,
  `noAdjacentFinsetCard` — the finset families that the counting theorems use.
-/

open Finset Function

/-- A binary string `f : Fin n → Bool` has no adjacent ones: whenever position `i` is
`true`, position `i+1` (if it exists) is `false`. -/
def NoAdjacentOnes {n : ℕ} (f : Fin n → Bool) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n), ¬ (f i ∧ f ⟨i.val + 1, h⟩)

/-- The finset of positions at which a binary string is `true`. -/
def supportFinset {n : ℕ} (f : Fin n → Bool) : Finset (Fin n) :=
  Finset.filter (fun x => f x = true) Finset.univ

/-- A finset of positions has no adjacent elements: whenever `x` belongs to it, the
next position (if it exists) does not. -/
def Finset.noAdjacent {n : ℕ} (s : Finset (Fin n)) : Prop :=
  ∀ (x : Fin n), x ∈ s → ∀ (h : x.val + 1 < n), (⟨x.val + 1, h⟩ : Fin n) ∉ s

/-- The canonical equivalence between binary functions on `Fin n` and finsets of
`Fin n`: a function is sent to the set of positions where it is `true`. -/
def boolFinsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun := supportFinset
  invFun := fun s x => (x ∈ s : Bool)
  left_inv := by
    intro f
    ext i
    simp [supportFinset]
  right_inv := by
    intro s
    ext i
    simp [supportFinset]

/-- The carrier of strictly monotone position tuples `g : Fin k ↪ Fin n` whose
successive values differ by at least two. These enumerate the length-`n` binary
strings with exactly `k` ones and no adjacent ones. -/
def GapMono (n k : ℕ) : Type :=
  { g : Fin k ↪ Fin n //
    ∀ (i : Fin k) (h : i.val + 1 < k), (g ⟨i.val + 1, h⟩).val ≥ (g i).val + 2 }

/-- `GapMono` is a finite type: it is a subtype of the finite type of embeddings. -/
noncomputable instance gapMonoFintype (n k : ℕ) : Fintype (GapMono n k) := by
  classical
  exact Subtype.fintype _

/-- Length-`n` binary strings with no adjacent ones. -/
noncomputable def noAdjacentStrings (n : ℕ) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter NoAdjacentOnes

/-- Length-`n` binary strings with no adjacent ones and exactly `k` ones. -/
noncomputable def noAdjacentStringsCard (n k : ℕ) : Finset (Fin n → Bool) := by
  classical
  exact (noAdjacentStrings n).filter fun f => (supportFinset f).card = k

/-- Finsets of positions in `Fin n` containing no two consecutive positions. -/
noncomputable def noAdjacentFinset (n : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter Finset.noAdjacent

/-- Finsets of positions in `Fin n` with no two consecutive positions and exactly
`k` elements. -/
noncomputable def noAdjacentFinsetCard (n k : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact (noAdjacentFinset n).filter fun s => s.card = k
