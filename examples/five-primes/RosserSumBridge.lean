import Mathlib

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

theorem psi_nat_eq_sum_range (x : ℕ) :
    Chebyshev.psi (x : ℝ) = ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hs : Finset.Icc 0 x = Finset.range (x + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hs]

end TaoFivePrimes
