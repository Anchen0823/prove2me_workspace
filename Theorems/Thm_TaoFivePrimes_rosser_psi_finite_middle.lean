import Mathlib.NumberTheory.Chebyshev

theorem TaoFivePrimes.rosser_psi_finite_middle (n : ℕ)
    (hn : 1000 < n) (hN : n < 10 ^ 8) :
    Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by sorry
