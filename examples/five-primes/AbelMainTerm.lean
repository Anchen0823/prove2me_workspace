import Mathlib

open MeasureTheory

namespace TaoFivePrimes

theorem quadratic_derivative_moment (a b A B : ℝ) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, (2 * (A * t + B) * A) * t) =
      (2 * A ^ 2 / 3) * (b ^ 3 - a ^ 3) + A * B * (b ^ 2 - a ^ 2) := by
  rw [← intervalIntegral.integral_of_le hab]
  have he : (fun t : ℝ => (2 * (A * t + B) * A) * t) =
      fun t => (2 * A ^ 2) * t ^ 2 + (2 * A * B) * t := by
    funext t
    ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun t : ℝ => (2 * A ^ 2) * t ^ 2)).intervalIntegrable a b)
    ((by fun_prop : Continuous (fun t : ℝ => (2 * A * B) * t)).intervalIntegrable a b)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_id]
  norm_num
  ring

theorem trapezoid_main_term (x : ℝ) (hx : 0 < x) :
    -(∫ t in Set.Ioc (x / 10) (x / 5),
        (2 * ((10 / x) * t + (-1)) * (10 / x)) * t) -
      (∫ t in Set.Ioc (4 * x / 5) (9 * x / 10),
        (2 * ((-10 / x) * t + 9) * (-10 / x)) * t) = (2 / 3) * x := by
  rw [quadratic_derivative_moment _ _ _ _ (by linarith),
    quadratic_derivative_moment _ _ _ _ (by linarith)]
  field_simp
  ring

end TaoFivePrimes
