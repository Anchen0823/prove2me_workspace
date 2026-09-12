import examples.«five-primes».CutoffEnergy

namespace TaoFivePrimes

/-- The squared trapezoid as three disjoint, left-open/right-closed pieces. -/
theorem eta1_sq_three_pieces (t : ℝ) :
    eta1 t ^ 2 =
      (if 1 / 10 < t ∧ t ≤ 1 / 5 then (10 * t - 1) ^ 2 else 0) +
      (if 1 / 5 < t ∧ t ≤ 4 / 5 then 1 else 0) +
      (if 4 / 5 < t ∧ t ≤ 9 / 10 then (9 - 10 * t) ^ 2 else 0) := by
  by_cases h0 : t ≤ 1 / 10
  · rw [eta1_left t (by linarith), max_eq_left (by linarith)]
    split_ifs <;> simp_all <;> linarith
  by_cases h1 : t ≤ 1 / 5
  · rw [eta1_left t h1, max_eq_right (by linarith)]
    split_ifs <;> simp_all <;> linarith
  by_cases h2 : t ≤ 4 / 5
  · rw [eta1_middle t ⟨by linarith, h2⟩]
    split_ifs <;> simp_all <;> linarith
  by_cases h3 : t ≤ 9 / 10
  · rw [eta1_right t (by linarith), max_eq_right (by linarith)]
    split_ifs <;> simp_all <;> linarith
  · rw [eta1_right t (by linarith), max_eq_left (by linarith)]
    split_ifs <;> simp_all <;> linarith

end TaoFivePrimes
