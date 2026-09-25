import Mathlib.NumberTheory.Chebyshev

/-! Mirror of the published Prove2Me theorem

  `TaoFivePrimes.rosser_schoenfeld_theta_lower_finite`  (status: Proved)
  theorem_id `37e2424b-e677-44ff-972d-1490e9e5062f`

Rosser--Schoenfeld (1962), Theorem 4, in the finite range.  The statement is
quoted verbatim from the platform; the body is a local placeholder only. -/

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_finite (t : ℝ) (h1 : 255 ≤ t) (h2 : t ≤ 1420) :
    t - 2 * Real.sqrt t < Chebyshev.theta t := by
  sorry

end TaoFivePrimes
