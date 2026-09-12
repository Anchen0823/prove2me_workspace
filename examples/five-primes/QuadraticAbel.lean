import Mathlib

open MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

theorem quadratic_vonMangoldt_abel (a b A B : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (A * (n : ℝ) + B) ^ 2 * (Λ n : ℝ)) =
      (A * b + B) ^ 2 * Chebyshev.psi b -
      (A * a + B) ^ 2 * Chebyshev.psi a -
      ∫ t in Set.Ioc a b, (2 * (A * t + B) * A) * Chebyshev.psi t := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => (A * t + B) ^ 2)
      (2 * (A * t + B) * A) t := by
    convert! (((hasDerivAt_id t).const_mul A).add_const B).pow 2 using 1 <;> simp
  have hder : deriv (fun t : ℝ => (A * t + B) ^ 2) =
      fun t => 2 * (A * t + B) * A := funext (fun t => (hd t).deriv)
  have hi : IntegrableOn (deriv (fun t : ℝ => (A * t + B) ^ 2)) (Set.Icc a b) := by
    rw [hder]
    exact (by fun_prop : Continuous (fun t : ℝ => 2 * (A * t + B) * A)).integrableOn_Icc
  have h := sum_mul_eq_sub_sub_integral_mul (fun n => (Λ n : ℝ)) ha hab
    (fun t _ => (hd t).differentiableAt) hi
  simpa only [hder, ← Chebyshev.psi_eq_sum_Icc] using h

end TaoFivePrimes
