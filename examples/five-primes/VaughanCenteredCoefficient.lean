import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Linarith

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- The centered divisor coefficient used in Tao's modified Vaughan identity.
The strict real cutoff matches the Type II coefficient in equation (4.19). -/
noncomputable def centeredVaughanCoefficient (V : ℝ) (w : ℕ) : ℝ :=
  (∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)), Λ b) - Real.log w / 2

/-- The factor one-half is essential for the explicit Type II constants. -/
theorem centeredVaughanCoefficient_abs_le (V : ℝ) (w : ℕ) :
    |centeredVaughanCoefficient V w| ≤ Real.log w / 2 := by
  have hlo : 0 ≤ ∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)), Λ b :=
    Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hhi : (∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)), Λ b) ≤ Real.log w := by
    rw [← ArithmeticFunction.vonMangoldt_sum]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _
    exact ArithmeticFunction.vonMangoldt_nonneg
  unfold centeredVaughanCoefficient
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TaoFivePrimes
