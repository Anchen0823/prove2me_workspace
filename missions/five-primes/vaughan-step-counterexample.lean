import Mathlib

/-!
# A formal counterexample to the absorption step in Tao's Lemma 4.11

Tao's proof of Lemma 4.11 (*Every odd number greater than 1 is the sum of at most
five primes*, arXiv:1201.6656v4, Section 4, printed p. 24) splits the third term of
the Vaughan identity as `g(w) + (1/2) log w` and absorbs the `(1/2) log w` half into
the Type I bucket `Σ_{d ≤ UV} |Σ_n (log n + c_d log d) F(dn)|`.  For a fixed index
`d` that step needs

  `(1/2) * |Σ_{w > V} log w · F(dw)|  ≤  |Σ_n log n · F(dn)|`,

where the left sum is restricted to `w > V` while the right one is not.

This file shows the inequality is false in general.  Take `d = 1`, `V = 40` and the
two-term weight `F = 1_{41} - 1_{39}` (supported at the odd integers 41 and 39).
Then the left-hand side is `(1/2) log 41 ≥ 20/41`, while the right-hand side is
`log 41 - log 39 = log (41/39) ≤ 2/39`; and `20/41 > 2/39`.

Nothing here depends on π, `exp` or numerical log bounds: the two inequalities used
are Mathlib's `Real.one_sub_inv_le_log_of_pos` and `Real.log_le_sub_one_of_pos`.

Context: this documents the gap in the open Prove2Me leaf
`TaoFivePrimes.theorem51_vaughan_split`; it is a statement about the *proof step*,
not about the leaf's statement, and it is kept local (not submitted as a platform
node).
-/

namespace TaoFivePrimes

/-- The two-term weight `F = 1_{41} - 1_{39}` (supported on odd integers, as in Tao's
setting where the smoothed sum runs over odd `n`). -/
def stepF (n : ℕ) : ℝ := if n = 41 then 1 else if n = 39 then -1 else 0

/-- The absorption step for `d = 1`, `V = 40`, `F = 1_{41} - 1_{39}` fails: the
restricted `w > V` sum on the left is not dominated by the unrestricted Type I
inner sum on the right. -/
theorem vaughan_step_absorbs_false :
    ¬ ((1 / 2 : ℝ) *
        |∑ w ∈ (Finset.Icc 41 41 : Finset ℕ), Real.log (w : ℝ) * stepF w| ≤
        |∑ n ∈ (Finset.Icc 39 41 : Finset ℕ), Real.log (n : ℝ) * stepF n|) := by
  have h41 : stepF 41 = 1 := by norm_num [stepF]
  have h39 : stepF 39 = -1 := by norm_num [stepF]
  have hset : (Finset.Icc 39 41 : Finset ℕ) = {39, 40, 41} := by decide
  have hL : (∑ w ∈ (Finset.Icc 41 41 : Finset ℕ), Real.log (w : ℝ) * stepF w) =
      Real.log 41 := by
    rw [Finset.Icc_self]
    simp [h41]
  have hR : (∑ n ∈ (Finset.Icc 39 41 : Finset ℕ), Real.log (n : ℝ) * stepF n) =
      Real.log 41 - Real.log 39 := by
    rw [hset]
    simp [stepF]
    ring
  have hRabs : |∑ n ∈ (Finset.Icc 39 41 : Finset ℕ), Real.log (n : ℝ) * stepF n| =
      Real.log 41 - Real.log 39 := by
    rw [hR, abs_of_nonneg]
    have hle : Real.log 39 ≤ Real.log 41 := Real.log_le_log (by norm_num) (by norm_num)
    linarith
  intro h
  rw [hL, hRabs] at h
  rw [abs_of_pos (Real.log_pos (by norm_num))] at h
  -- `(1/2) log 41 ≥ 20/41` while `log 41 - log 39 = log (41/39) ≤ 2/39`, and `20/41 > 2/39`.
  have hlow : (20 : ℝ) / 41 ≤ (1 / 2) * Real.log 41 := by
    have h1 : 1 - (41 : ℝ)⁻¹ ≤ Real.log 41 := Real.one_sub_inv_le_log_of_pos (by norm_num)
    have h2 : (1 : ℝ) - (41 : ℝ)⁻¹ = 40 / 41 := by norm_num
    rw [h2] at h1
    linarith
  have hup : Real.log 41 - Real.log 39 ≤ 2 / 39 := by
    have hd : Real.log (41 / 39 : ℝ) = Real.log 41 - Real.log 39 :=
      Real.log_div (by norm_num) (by norm_num)
    rw [← hd]
    have h1 : Real.log (41 / 39 : ℝ) ≤ 41 / 39 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : (41 : ℝ) / 39 - 1 = 2 / 39 := by norm_num
    linarith
  linarith

end TaoFivePrimes
