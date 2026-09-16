import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51VinogradovSharp

/-- Local mirror of the platform node `a260b5dc` (Open, SKETCH_ACCEPTED). -/
theorem TaoFivePrimes.vinogradov_odd_sharp
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A alpha beta theta x y : ℝ) (a' : ℤ) (hA : 0 ≤ A)
    (ha'q : Nat.Coprime a'.natAbs q)
    (halpha : 2 * alpha = (a' : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hwidth : y ≤ x + 2 * (q : ℝ)) :
    (∑ z ∈ (TaoFivePrimesVinogradovSharp.zIoc x y).filter (fun z => Odd z),
        TaoFivePrimesVinogradovSharp.vmin A B alpha theta z)
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  sorry
