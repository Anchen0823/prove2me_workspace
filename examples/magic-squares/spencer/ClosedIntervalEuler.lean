import examples.«magic-squares».spencer.ClosedIntervalValuation

set_option autoImplicit false

namespace MagicSquaresEuler

open Finset

/-- A nondegenerate open interval is its closed interval with the two endpoint
singletons removed, at the level of rational-valued indicator functions. -/
theorem openInterval_indicator_eq_closed_sub_endpoints
    (a b x : ℝ) (hab : a < b) :
    (if a < x ∧ x < b then (1 : ℚ) else 0) =
      (if a ≤ x ∧ x ≤ b then (1 : ℚ) else 0) -
        (if x = a then (1 : ℚ) else 0) -
          (if x = b then (1 : ℚ) else 0) := by
  by_cases hax : a < x <;> by_cases hxb : x < b
  · simp [hax, hxb, ne_of_gt hax, ne_of_lt hxb, hax.le, hxb.le]
  · have hbx : b ≤ x := le_of_not_gt hxb
    have hxa : x ≠ a := ne_of_gt (lt_of_lt_of_le hab hbx)
    by_cases h : x = b
    · subst x
      simp [hab.ne', hab.le]
    · have hnot : ¬x ≤ b := fun hle => h (le_antisymm hle hbx)
      simp [hax, hxb, hxa, h, hnot]
  · have hxa : x ≤ a := le_of_not_gt hax
    have hxb' : x ≠ b := ne_of_lt (lt_of_le_of_lt hxa hab)
    by_cases h : x = a
    · subst x
      simp [hab.ne, hab.le]
    · have hnot : ¬a ≤ x := fun hle => h (le_antisymm hxa hle)
      simp [hax, hxb, h, hxb', hnot]
  · have hxa : x ≤ a := le_of_not_gt hax
    have hbx : b ≤ x := le_of_not_gt hxb
    exact False.elim (not_lt_of_ge (hbx.trans hxa) hab)

/-- Pointwise equal finite linear combinations of nonempty closed intervals and
singletons have equal total coefficients.  Singletons are included explicitly
because they are the endpoint terms in the open-interval identity above. -/
theorem closedInterval_singleton_total_coeff_eq
    {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ]
    [Fintype ι'] [Fintype κ']
    (a b : ι → ℝ) (w : ι → ℚ) (p : κ → ℝ) (v : κ → ℚ)
    (a' b' : ι' → ℝ) (w' : ι' → ℚ) (p' : κ' → ℝ) (v' : κ' → ℚ)
    (hab : ∀ i, a i ≤ b i) (hab' : ∀ i, a' i ≤ b' i)
    (h : ∀ x : ℝ,
      (∑ i, if a i ≤ x ∧ x ≤ b i then w i else 0) +
          (∑ j, if x = p j then v j else 0) =
        (∑ i, if a' i ≤ x ∧ x ≤ b' i then w' i else 0) +
          (∑ j, if x = p' j then v' j else 0)) :
    (∑ i, w i) + ∑ j, v j = (∑ i, w' i) + ∑ j, v' j := by
  classical
  let A : (ι ⊕ κ) ⊕ (ι' ⊕ κ') → ℝ
    | Sum.inl (Sum.inl i) => a i
    | Sum.inl (Sum.inr j) => p j
    | Sum.inr (Sum.inl i) => a' i
    | Sum.inr (Sum.inr j) => p' j
  let B : (ι ⊕ κ) ⊕ (ι' ⊕ κ') → ℝ
    | Sum.inl (Sum.inl i) => b i
    | Sum.inl (Sum.inr j) => p j
    | Sum.inr (Sum.inl i) => b' i
    | Sum.inr (Sum.inr j) => p' j
  let W : (ι ⊕ κ) ⊕ (ι' ⊕ κ') → ℚ
    | Sum.inl (Sum.inl i) => w i
    | Sum.inl (Sum.inr j) => v j
    | Sum.inr (Sum.inl i) => -w' i
    | Sum.inr (Sum.inr j) => -v' j
  have hAB : ∀ z, A z ≤ B z := by
    intro z
    rcases z with (i | j) | (i | j)
    · exact hab i
    · exact le_rfl
    · exact hab' i
    · exact le_rfl
  have hzero : ∀ x : ℝ,
      (∑ z, if A z ≤ x ∧ x ≤ B z then W z else 0) = 0 := by
    intro x
    have hs (q : ℝ) (c : ℚ) :
        (if q ≤ x ∧ x ≤ q then c else 0) = (if x = q then c else 0) := by
      by_cases hx : x = q
      · simp [hx]
      · have hn : ¬(q ≤ x ∧ x ≤ q) := fun hq => hx (le_antisymm hq.2 hq.1)
        simp [hx, hn]
    have hn (P : Prop) [Decidable P] (c : ℚ) :
        (if P then -c else 0) = -(if P then c else 0) := by
      by_cases hP : P <;> simp [hP]
    simp only [Fintype.sum_sum_type, A, B, W]
    simp_rw [hs]
    simp_rw [hn]
    simp only [sum_neg_distrib]
    linarith [h x]
  have hsum := closedInterval_indicator_relation A B W hAB hzero
  simp only [Fintype.sum_sum_type, W, sum_neg_distrib] at hsum
  linarith

end MagicSquaresEuler
