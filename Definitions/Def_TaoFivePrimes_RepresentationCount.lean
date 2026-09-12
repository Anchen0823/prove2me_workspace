import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Primorial
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The weighted representation count in Tao's five-primes proof

Source: Terence Tao, https://arxiv.org/abs/1201.6656, equations (1.7), (8.10),
and the definition of η₁ at the beginning of Section 8. The proof fixes `K = 1000`.
Natural division gives the integer bounds in the finite sums. Primorial cutoffs
are inclusive, as in the paper's Section 2 conventions.
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- Tao's logarithmic cutoff, extended by zero to nonpositive arguments. -/
noncomputable def eta0 (t : ℝ) : ℝ :=
  if 0 < t then 4 * max 0 (Real.log 2 - |Real.log (2 * t)|) else 0

/-- The trapezoidal cutoff used for the first two primes in Section 8. -/
noncomputable def eta1 (t : ℝ) : ℝ :=
  max 0 (1 - 10 * Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5)))

/-- Von Mangoldt with all prime factors at most `sqrt N` removed. -/
noncomputable def siftedVonMangoldt (N n : ℕ) : ℝ :=
  if n.Coprime (primorial (Nat.sqrt N)) then Λ n else 0

/-- Equation (8.10), at `K = 1000`, with a general gap budget `H`.
The three positive shifts each have upper bound `H / 3`. -/
noncomputable def representationCount (x H : ℕ) : ℝ :=
  ∑ n₁ ∈ Finset.range (x + 1),
  ∑ n₂ ∈ Finset.range (x + 1),
  ∑ n₃ ∈ Finset.range (x / 1000 + 1),
  ∑ h₁ ∈ Finset.Icc 1 (H / 3),
  ∑ h₂ ∈ Finset.Icc 1 (H / 3),
  ∑ h₃ ∈ Finset.Icc 1 (H / 3),
    if x = n₁ + n₂ + n₃ + h₁ + h₂ + h₃ then
      siftedVonMangoldt x n₁ * eta1 ((n₁ : ℝ) / x) *
      siftedVonMangoldt x n₂ * eta1 ((n₂ : ℝ) / x) *
      siftedVonMangoldt (x / 1000) n₃ * eta0 (1000 * (n₃ : ℝ) / x)
    else 0

end TaoFivePrimes
