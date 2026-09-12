import examples.«five-primes».QuadraticAbel

open MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- Abel summation for the three polynomial pieces; all boundary terms cancel. -/
theorem trapezoid_piecewise_abel (x : ℝ) (hx : 0 < x) :
    (∑ n ∈ Finset.Ioc ⌊x / 10⌋₊ ⌊x / 5⌋₊,
      ((10 / x) * (n : ℝ) + (-1)) ^ 2 * (Λ n : ℝ)) +
    (∑ n ∈ Finset.Ioc ⌊x / 5⌋₊ ⌊4 * x / 5⌋₊, (Λ n : ℝ)) +
    (∑ n ∈ Finset.Ioc ⌊4 * x / 5⌋₊ ⌊9 * x / 10⌋₊,
      ((-10 / x) * (n : ℝ) + 9) ^ 2 * (Λ n : ℝ)) =
    -(∫ t in Set.Ioc (x / 10) (x / 5),
        (2 * ((10 / x) * t + (-1)) * (10 / x)) * Chebyshev.psi t) -
      ∫ t in Set.Ioc (4 * x / 5) (9 * x / 10),
        (2 * ((-10 / x) * t + 9) * (-10 / x)) * Chebyshev.psi t := by
  have h1 := quadratic_vonMangoldt_abel (x / 10) (x / 5) (10 / x) (-1)
    (by positivity) (by linarith)
  have h2 := quadratic_vonMangoldt_abel (x / 5) (4 * x / 5) 0 1
    (by positivity) (by linarith)
  have h3 := quadratic_vonMangoldt_abel (4 * x / 5) (9 * x / 10) (-10 / x) 9
    (by positivity) (by linarith)
  have e1 : (10 / x) * (x / 10) + (-1) = 0 := by field_simp; ring
  have e2 : (10 / x) * (x / 5) + (-1) = 1 := by field_simp; ring
  have e3 : (-10 / x) * (4 * x / 5) + 9 = 1 := by field_simp; ring
  have e4 : (-10 / x) * (9 * x / 10) + 9 = 0 := by field_simp; ring
  simp only [e1, e2, e3, e4, zero_pow (by norm_num : 2 ≠ 0), one_pow,
    zero_mul, one_mul, sub_zero, zero_sub] at h1 h3
  simp only [zero_mul, zero_add, one_pow, one_mul, mul_zero,
    integral_zero, sub_zero] at h2
  linarith

end TaoFivePrimes
