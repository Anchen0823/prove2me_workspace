import examples.«five-primes».AbelMainTerm

open MeasureTheory

namespace TaoFivePrimes

theorem quadratic_derivative_integral (a b A B : ℝ) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, 2 * (A * t + B) * A) =
      (A * b + B) ^ 2 - (A * a + B) ^ 2 := by
  rw [← intervalIntegral.integral_of_le hab]
  have he : (fun t : ℝ => 2 * (A * t + B) * A) =
      fun t => (2 * A ^ 2) * t + (2 * A * B) := by funext t; ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun t : ℝ => (2 * A ^ 2) * t)).intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b)]
  rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem trapezoid_kernel_integrals (x : ℝ) (hx : 0 < x) :
    (∫ t in Set.Ioc (x / 10) (x / 5), 2 * ((10 / x) * t + (-1)) * (10 / x)) = 1 ∧
    (∫ t in Set.Ioc (4 * x / 5) (9 * x / 10),
      -(2 * ((-10 / x) * t + 9) * (-10 / x))) = 1 := by
  constructor
  · rw [quadratic_derivative_integral _ _ _ _ (by linarith)]
    field_simp
    ring
  · rw [integral_neg, quadratic_derivative_integral _ _ _ _ (by linarith)]
    field_simp
    ring

end TaoFivePrimes
