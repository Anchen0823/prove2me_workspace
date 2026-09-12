import Mathlib

namespace TaoFivePrimes

/-- The explicit two-sided estimate also supplies the large-argument Rosser bound. -/
theorem psi_lt_rosser_of_error (y : ℝ) (hy : 10 ^ 8 ≤ y)
    (he : |Chebyshev.psi y - y| ≤ y / (40 * Real.log y)) :
    Chebyshev.psi y < 1.03883 * y := by
  have hy0 : 0 ≤ y := by linarith
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (show (4 : ℝ) ≤ y by linarith)
  have hlog : 1 ≤ Real.log y := by norm_num at htwo; linarith
  have hdiv : y / (40 * Real.log y) ≤ y / 40 :=
    div_le_div_of_nonneg_left hy0 (by norm_num) (by linarith)
  have herr := (abs_le.mp he).2
  linarith

/-- A finite certificate and the large-argument source cover every positive integer. -/
theorem rosser_of_finite_and_error
    (hfinite : ∀ n : ℕ, 0 < n → n < 10 ^ 8 →
      Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ))
    (hsource : ∀ y : ℝ, 10 ^ 8 ≤ y →
      |Chebyshev.psi y - y| ≤ y / (40 * Real.log y)) :
    ∀ n : ℕ, 0 < n → Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by
  intro n hn
  by_cases hsmall : n < 10 ^ 8
  · exact hfinite n hn hsmall
  · have hlarge : (10 ^ 8 : ℝ) ≤ n := by exact_mod_cast (show 10 ^ 8 ≤ n by omega)
    exact psi_lt_rosser_of_error (n : ℝ) hlarge (hsource n hlarge)

end TaoFivePrimes
