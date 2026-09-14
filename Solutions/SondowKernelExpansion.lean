import Definitions.Def_eulerMascheroni_sondowCutoff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

open Finset

namespace EulerMascheroni.Sondow

theorem weighted_binomial_expansion (n : ℕ) (x : ℝ) :
    (x*(1-x))^n = ∑ i ∈ range (n+1),
      ((-1:ℝ)^i*(n.choose i:ℝ)) * x^(n+i) := by
  rw [mul_pow, show 1-x = -x+1 by ring, add_pow, mul_sum]
  apply sum_congr rfl
  intro i hi
  simp only [one_pow, mul_one, pow_add]
  rw [neg_pow]
  ring

theorem numerator_expansion (n : ℕ) (x y : ℝ) :
    (x*(1-x)*y*(1-y))^n =
      ∑ i ∈ range (n+1), ∑ j ∈ range (n+1),
        ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) *
          (x^(n+i)*y^(n+j)) := by
  rw [show x*(1-x)*y*(1-y) = (x*(1-x))*(y*(1-y)) by ring,
    mul_pow, weighted_binomial_expansion, weighted_binomial_expansion, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- Exact pointwise finite expansion away from the geometric pole. -/
theorem truncated_kernel_expansion (n N : ℕ) (x y : ℝ) (hxy : x*y ≠ 1) :
    (x*(1-x)*y*(1-y))^n / ((1-x*y)*(-Real.log (x*y))) * (1-(x*y)^N) =
      ∑ i ∈ range (n+1), ∑ j ∈ range (n+1), ∑ v ∈ range N,
        ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) *
          (x^(n+i+v)*y^(n+j+v)/(-Real.log (x*y))) := by
  rw [← geom_sum_mul_neg (x*y) N]
  have hden : 1-x*y ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  rw [show (x*(1-x)*y*(1-y))^n / ((1-x*y)*(-Real.log (x*y))) *
      ((∑ v ∈ range N, (x*y)^v)*(1-x*y)) =
      (x*(1-x)*y*(1-y))^n * (∑ v ∈ range N, (x*y)^v) / (-Real.log (x*y)) by
        field_simp]
  rw [numerator_expansion, sum_mul, sum_div]
  apply sum_congr rfl
  intro i hi
  rw [sum_mul, sum_div]
  apply sum_congr rfl
  intro j hj
  rw [mul_sum, sum_div]
  apply sum_congr rfl
  intro v hv
  simp only [pow_add, mul_pow]
  ring

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.weighted_binomial_expansion
#print axioms EulerMascheroni.Sondow.numerator_expansion
#print axioms EulerMascheroni.Sondow.truncated_kernel_expansion
