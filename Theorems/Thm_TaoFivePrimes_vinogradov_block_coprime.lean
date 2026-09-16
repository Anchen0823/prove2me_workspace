import Mathlib

/-- Local mirror of the platform node `32cd79af` (Open). -/
theorem TaoFivePrimes.vinogradov_block_coprime
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' beta' theta' : ℝ) (a' : ℤ) (hA' : 0 ≤ A')
    (ha'q : Nat.Coprime a'.natAbs q)
    (halpha' : alpha' = (a' : ℝ) / q + beta') (hbeta' : |beta'| ≤ 1 / (q : ℝ) ^ 2)
    (m : ℤ) :
    (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  sorry
