import Mathlib.NumberTheory.Chebyshev

-- Unpublished local source placeholder; not a proved theorem.
-- Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers,
-- Illinois J. Math. 6 (1962), Theorem 4, eq. (3.14), restricted to 1420 <= t <= 10^8.
namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_analytic_finite (t : ℝ) (h1 : 1420 ≤ t)
    (h2 : t ≤ 10 ^ 8) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by sorry

end TaoFivePrimes
