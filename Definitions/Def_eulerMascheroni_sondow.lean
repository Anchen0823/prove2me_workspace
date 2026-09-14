import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace EulerMascheroni.Sondow
open Finset

def d (n : ℕ) : ℕ := (Icc 1 n).lcm id

def A (n : ℕ) : ℚ :=
  ∑ i ∈ range (n + 1), (n.choose i : ℚ)^2 * harmonic (n + i)

-- Sondow (2002), equation (8); all three summation ranges are inclusive.
def L (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, ∑ i ∈ Icc 0 (min (k - 1) (n - k)),
    ∑ j ∈ Icc (i + 1) (n - i),
      2 * (n.choose i : ℝ)^2 / (j : ℝ) * Real.log (n + k : ℕ)

def I (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
    (x * (1 - x) * y * (1 - y))^n / ((1 - x*y) * (-Real.log (x*y)))

end EulerMascheroni.Sondow
