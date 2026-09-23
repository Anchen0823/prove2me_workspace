import examples.«magic-squares».spencer.ClosedIntervalValuation

set_option autoImplicit false

namespace MagicSquaresEuler

attribute [local instance] Classical.propDecidable

/-- The one-dimensional Euler relation, allowing empty compact convex sets. -/
theorem compactReal_indicator_relation {ι : Type*} [Fintype ι]
    (K : ι → Set ℝ) (w : ι → ℚ)
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (h : ∀ x : ℝ, (∑ i, if x ∈ K i then w i else 0) = 0) :
    (∑ i, if (K i).Nonempty then w i else 0) = 0 := by
  classical
  let a : ι → ℝ := fun i => if (K i).Nonempty then sInf (K i) else 0
  let b : ι → ℝ := fun i => if (K i).Nonempty then sSup (K i) else 0
  let v : ι → ℚ := fun i => if (K i).Nonempty then w i else 0
  have hK (i : ι) (hi : (K i).Nonempty) : K i = Set.Icc (a i) (b i) := by
    simpa [a, b, hi] using eq_Icc_of_connected_compact ((hv i).isConnected hi) (hc i)
  have hab (i : ι) : a i ≤ b i := by
    by_cases hi : (K i).Nonempty
    · exact Set.nonempty_Icc.mp ((hK i hi) ▸ hi)
    · simp [a, b, hi]
  apply closedInterval_indicator_relation a b v hab
  intro x
  convert h x using 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (K i).Nonempty
  · simp only [v, if_pos hi]
    rw [hK i hi]
    simp only [Set.mem_Icc]
  · have hx : x ∉ K i := fun hx => hi ⟨x, hx⟩
    simp [v, hi, hx]

end MagicSquaresEuler
