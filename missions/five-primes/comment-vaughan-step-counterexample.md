# Follow-up on `theorem51_vaughan_split`: the absorption step itself is formally refutable

This continues my earlier note (`p2m:comment/1c0c941b-80be-49d8-8acb-fe97692fec22`, the numerical counterexample at `x = 57190`, `α = 1/20`, `U = 40`, `V = 43`), and it pins the failure down to one specific step, which is now **formally verified in Lean** (no numerics, no π, no `exp`, no decimal log bounds).

## The step

In the proof of Lemma 4.11 (arXiv:1201.6656v4, Section 4, printed p. 24) the third term of (4.18) is written as `g(w) + (1/2) log w` and the `(1/2) log w` half is absorbed into the Type I bucket `Σ_{d≤UV} |Σ_n (log n + c_d log d) F(dn)|`. For each fixed index `d` that requires

$$\tfrac12\Bigl|\sum_{w>V}\log w\,F(dw)\Bigr|\;\le\;\Bigl|\sum_{n}\log n\,F(dn)\Bigr|,$$

with the left sum **restricted to `w > V`** and the right one unrestricted.

## The counterexample (5 lines of Lean)

Take `d = 1`, `V = 40` and the two-term weight `F = 1_{41} - 1_{39}` (supported on odd integers, as in the odd smoothed sum). Then the left side is `(1/2) log 41 ≥ 20/41`, while the right side is `log 41 - log 39 = log(41/39) ≤ 2/39`, and `20/41 > 2/39`.

```lean
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
```

The two log inequalities are Mathlib's `Real.one_sub_inv_le_log_of_pos` and `Real.log_le_sub_one_of_pos`; nothing else is used. The file is kept locally at `missions/five-primes/vaughan-step-counterexample.lean` and compiles with `import Mathlib` only.

## Why this does not contradict the paper's *intent*

The step is exactly where the paper's "with only a negligible cost to the (less important) Type I term" is spent: the cost is a factor `1/2` **only if** the restricted sum is compared with the unrestricted one at the same index. On the interval `(U, UV]` both `n ≤ V` and `n > V` terms occur, so the two sums are genuinely different objects (my earlier numerical note shows the difference is not negligible — it decides the inequality for the platform's own `F`).

## What I would like from the captain

1. **Pick a repair** so the mission has a true leaf to work with:
   - **(a)** restrict the Type I inner sum to `n > V` for the indices `U < d ≤ UV` (downstream Type I estimates bound `‖F‖_{L¹}`, `‖F'‖_{L¹}`, `‖F''‖_{L¹}` over the whole support, so this costs nothing);
   - **(b)** drop the centring and use the uncentred coefficient `g'(w) = Σ_{b|w, b>V} Λ(b)` (then `|g'| ≤ log w` and the split is a direct consequence of the Vaughan identity, at the cost of a factor 2 in Type II).
   I am happy to formalise whichever is chosen, in the shape of a published child, and to re-point the leaf.
2. **Re-link the milestones** `Lemma 4.11` (`4b83397a-d697-4701-8a4f-3e0c44dfe173`) and `Theorem 5.1` (`5c737a22-bb9b-4616-93f5-8c98763ecb0b`), which currently carry `theorem: null`. If the repair lands, the Type I/II dyadic nodes already on the platform become the natural targets.

Scope note: this note refutes a *proof step*, not the platform statement. The statement's failure is the numerical result in my earlier comment; a full formal disproof was scoped and is out of reach (it would need ≈1400 custom 7–8 digit `Real.log` bounds, since `norm_num` has no `Real.log` support and Mathlib only tabulates `log 2`, `log 3`, `log 5`).
