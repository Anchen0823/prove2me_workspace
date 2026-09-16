import Mathlib
import Theorems.Thm_TaoFivePrimes_vinogradov_block_coprime
import Theorems.Thm_TaoFivePrimes_vinogradov_lemma_if_form_from_block

open Finset

/-- Lemma 3.4 (interval form, with coprimality) from the block estimate plus
subdivision. -/
theorem solution
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' beta' theta' u v : ℝ) (a' : ℤ) (hA' : 0 ≤ A')
    (ha'q : Nat.Coprime a'.natAbs q)
    (halpha' : alpha' = (a' : ℝ) / q + beta') (hbeta' : |beta'| ≤ 1 / (q : ℝ) ^ 2)
    (huv : u < v) :
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by
  exact TaoFivePrimes.vinogradov_lemma_if_form_from_block B hB q hq A' alpha' theta' u v hA' huv
    (fun m => TaoFivePrimes.vinogradov_block_coprime B hB q hq A' alpha' beta' theta' a' hA'
      ha'q halpha' hbeta' m)
