import Mathlib

namespace TaoFivePrimes

/-- Specialize the three logarithmic factors in Theorem 5.1. -/
theorem large_q_log_specialization (x U V : ℝ) (hx : 0 < x) (hV : 0 < V)
    (hU : U = x / V ^ 2) :
    Real.log (x / (U * V)) = Real.log V ∧
    Real.log (V * x / U) = 3 * Real.log V ∧
    Real.log (x / U) = 2 * Real.log V := by
  have h1 : x / (U * V) = V := by rw [hU]; field_simp
  have h2 : V * x / U = V ^ 3 := by rw [hU]; field_simp
  have h3 : x / U = V ^ 2 := by rw [hU]; field_simp
  rw [h1, h2, h3, Real.log_pow, Real.log_pow]
  norm_num

end TaoFivePrimes
