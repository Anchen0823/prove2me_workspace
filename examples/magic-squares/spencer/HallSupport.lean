/-
# Brick 3: the support of a semi-magic square contains a permutation

Spencer's proof of polynomiality runs a recursion over the *support sets*
`B(T) = {(i,j) : T(i,j) ≥ 1}` of semi-magic squares, ordered by inclusion.  The recursion
step removes from such a square the 0/1 matrix of a permutation contained in its support, and
for that to be possible every support set must contain one.  That is exactly Hall's marriage
theorem, and the zbMATH review of Spencer's note lists "marriage theorem" among its keywords.

This brick proves the input in the form the recursion needs it:

  if `M` is an `n × n` matrix of nonnegative integers whose rows and columns all sum to the
  same *positive* `t`, then there is a permutation `σ` with `0 < M i (σ i)` for all `i`.

Positivity of `t` is essential: the zero matrix has the empty support and no permutation in it,
which is the source of the boundary subtlety recorded in `SPENCER-ROUTE.md` §4.1.

Scratch file, compiled with `lake env lean`.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000

open Finset

namespace MagicSquaresSpencer

/-- **The Birkhoff–von Neumann/marriage input for Spencer's proof.**  The support of a
nonnegative integer matrix with all rows and columns summing to the same positive `t` contains
the support of a permutation matrix. -/
theorem exists_perm_pos_of_line_sums {n t : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) (ht : 0 < t)
    (hrow : ∀ i : Fin n, ∑ j : Fin n, M i j = t)
    (hcol : ∀ j : Fin n, ∑ i : Fin n, M i j = t) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, 0 < M i (σ i) := by
  classical
  set supp : Fin n → Finset (Fin n) := fun i => Finset.univ.filter fun j => 0 < M i j with hsupp
  have hmem : ∀ i j : Fin n, j ∈ supp i ↔ 0 < M i j := by
    intro i j
    rw [hsupp]
    simp
  have hhall : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion supp).card := by
    intro s
    have key : s.card * t ≤ (s.biUnion supp).card * t := by
      calc s.card * t = ∑ i ∈ s, ∑ j : Fin n, M i j := by
            rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, smul_eq_mul]
        _ = ∑ i ∈ s, ∑ j ∈ s.biUnion supp, M i j := by
            refine (Finset.sum_congr rfl fun i hi => ?_).symm
            refine Finset.sum_subset (fun j _ => Finset.mem_univ j) fun j _ hj => ?_
            by_contra hne
            exact hj (Finset.mem_biUnion.mpr ⟨i, hi, (hmem i j).mpr (Nat.pos_of_ne_zero hne)⟩)
        _ = ∑ j ∈ s.biUnion supp, ∑ i ∈ s, M i j := Finset.sum_comm
        _ ≤ ∑ j ∈ s.biUnion supp, ∑ i : Fin n, M i j := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact Finset.sum_le_sum_of_subset_of_nonneg (fun i _ => Finset.mem_univ i)
              fun i _ _ => Nat.zero_le _
        _ = ∑ j ∈ s.biUnion supp, t := by
            exact Finset.sum_congr rfl fun j _ => hcol j
        _ = (s.biUnion supp).card * t := by
            rw [Finset.sum_const, smul_eq_mul]
    exact Nat.le_of_mul_le_mul_right key ht
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective supp).mp hhall
  refine ⟨Equiv.ofBijective f ?_, fun i => (hmem i (f i)).mp (hf i)⟩
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨hfinj, rfl⟩

end MagicSquaresSpencer
