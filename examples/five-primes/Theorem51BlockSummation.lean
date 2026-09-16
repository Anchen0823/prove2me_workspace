import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Definitions.Def_TaoFivePrimes_Theorem51Sums

/-!
# Tao Section 5: summing the Type I pointwise envelope over blocks

Source: T. Tao, *Every odd number greater than 1 is the sum of at most five
primes*, arXiv:1201.6656v4, Section 5, step (5.14) -> (5.17), pp. 26--28.

This isolates the combinatorial/analytic half of the Type I estimate: passing
from a pointwise envelope for a nonnegative weight `W` on the positive odd
`d ≤ UV` to the two-term bound of Theorem 5.1. It carries no information about
the exponential sums themselves.

Scratch module: not yet assembled into a submission.
-/

open Finset

namespace TaoFivePrimes

/-- The first alternative of the (5.14) envelope. -/
noncomputable def typeIAlt (x d : ℝ) : ℝ :=
  (1 / 2) * (x / d) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)

/-- The second alternative of the (5.14) envelope, with the phase variable
`t = 2αd` made explicit. -/
noncomputable def typeIAlt' (x t : ℝ) : ℝ :=
  4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * t)|

end TaoFivePrimes
