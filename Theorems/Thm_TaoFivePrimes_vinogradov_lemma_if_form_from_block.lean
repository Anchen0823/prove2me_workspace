import Mathlib

/-- Local mirror of the platform node `90cf0471` (Proved on the platform).

    This file is a **mirror only**: it records the statement so that local
    solutions can import it, and its body is `by sorry` by repository
    convention (see `MEMORY.md`).  The actual proof lives on the platform;
    nothing here has been verified in this repository. -/
theorem TaoFivePrimes.vinogradov_lemma_if_form_from_block
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' theta' u v : ℝ) (hA' : 0 ≤ A') (huv : u < v)
    (hblock : ∀ m : ℤ,
      (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
          (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
            else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
        ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) :
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by
  sorry

open Finset
