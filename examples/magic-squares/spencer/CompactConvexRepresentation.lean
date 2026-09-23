import examples.«magic-squares».spencer.CompactConvexValuation

set_option autoImplicit false

namespace MagicSquaresEuler

attribute [local instance] Classical.propDecidable

/-- Two finite rational presentations by indicators of compact convex sets
assign the same total coefficient to their nonempty terms whenever they agree
pointwise. -/
theorem compactConvex_representation_total_coeff_eq (n : ℕ)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → Set (Fin n → ℝ)) (w : ι → ℚ)
    (K' : κ → Set (Fin n → ℝ)) (w' : κ → ℚ)
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (hc' : ∀ j, IsCompact (K' j)) (hv' : ∀ j, Convex ℝ (K' j))
    (h : ∀ x,
      (∑ i, if x ∈ K i then w i else 0) =
        ∑ j, if x ∈ K' j then w' j else 0) :
    (∑ i, if (K i).Nonempty then w i else 0) =
      ∑ j, if (K' j).Nonempty then w' j else 0 := by
  classical
  let sets : ι ⊕ κ → Set (Fin n → ℝ)
    | Sum.inl i => K i
    | Sum.inr j => K' j
  let weights : ι ⊕ κ → ℚ
    | Sum.inl i => w i
    | Sum.inr j => -w' j
  have hcompact : ∀ z, IsCompact (sets z) := by
    intro z
    rcases z with i | j
    · exact hc i
    · exact hc' j
  have hconvex : ∀ z, Convex ℝ (sets z) := by
    intro z
    rcases z with i | j
    · exact hv i
    · exact hv' j
  have hzero : ∀ x,
      (∑ z, if x ∈ sets z then weights z else 0) = 0 := by
    intro x
    have hneg (P : Prop) [Decidable P] (c : ℚ) :
        (if P then -c else 0) = -(if P then c else 0) := by
      by_cases hP : P <;> simp [hP]
    simp only [Fintype.sum_sum_type, sets, weights]
    simp_rw [hneg]
    rw [Finset.sum_neg_distrib]
    simpa only [sub_eq_add_neg] using sub_eq_zero.mpr (h x)
  have htotal := compactConvex_indicator_relation n sets weights
    hcompact hconvex hzero
  have hneg (P : Prop) [Decidable P] (c : ℚ) :
      (if P then -c else 0) = -(if P then c else 0) := by
    by_cases hP : P <;> simp [hP]
  simp only [Fintype.sum_sum_type, sets, weights] at htotal
  simp_rw [hneg] at htotal
  rw [Finset.sum_neg_distrib] at htotal
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using htotal)

end MagicSquaresEuler
