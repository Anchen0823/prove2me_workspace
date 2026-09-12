import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Mathlib

namespace TaoFivePrimes
open Finset

noncomputable def oddHalfInterval (A B : ℝ) : Finset ℤ :=
  Icc ⌈(A - 1) / 2⌉ ⌊(B - 1) / 2⌋

noncomputable def oddRealInterval (A B : ℝ) : Finset ℤ :=
  (oddHalfInterval A B).image (fun n => 2 * n + 1)

noncomputable def scaleRowCoefficient (V : ℝ) (w : ℤ) : ℂ :=
  if V < (w : ℝ) then (theorem51Centered V w.toNat : ℂ) else 0

noncomputable def scaleColumnCoefficient (U : ℝ) (n : ℤ) : ℂ :=
  if U < ((2 * n + 1 : ℤ) : ℝ) then
    (ArithmeticFunction.moebius (2 * n + 1).toNat : ℂ) else 0

noncomputable def theorem51ScaleSum (x alpha U V W : ℝ) : ℂ :=
  ∑ w ∈ oddRealInterval (W / 2) W, scaleRowCoefficient V w *
    (∑ n ∈ oddHalfInterval (x / (2 * W)) (x / W),
      expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * scaleColumnCoefficient U n)

end TaoFivePrimes

