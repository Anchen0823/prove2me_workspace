import Mathlib.NumberTheory.Chebyshev

/-! Local placeholder for the new child theorem proposed together with the
reduction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic`.

`rosser_schoenfeld_theta_lower_analytic_mid` is the middle, finite range
1420 <= t <= 10^10 of Rosser--Schoenfeld (1962) (3.14).  It is the only new
obligation that the reduction does not discharge: the range 1340 <= t <= 1420
is covered by the already-proved platform theorem
`TaoFivePrimes.rosser_schoenfeld_theta_lower_finite`, and the unbounded range
t >= 10^10 follows from the already-published platform input
`TaoFivePrimes.schoenfeld_psi_error_large` together with Mathlib's
`Chebyshev.psi_sub_theta_le`. -/

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_analytic_mid (t : ℝ) (h1 : 1420 ≤ t)
    (h2 : t ≤ 10 ^ 10) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by
  sorry

end TaoFivePrimes
