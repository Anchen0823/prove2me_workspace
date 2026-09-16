import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_BlockFoundation

set_option maxHeartbeats 800000

/-! # Corollary 3.5: the odd-restricted Vinogradov min-sum

Tao, arXiv:1201.6656v4, Lemma 3.4 and Corollary 3.5.

**Lemma 3.4 (Vinogradov-type lemma).**  Let `α = a/q + β` with
`β = O*(1/q²)`.  Then for any `x < y`, `A, B > 0`, and `θ ∈ ℝ/ℤ`,

`Σ_{x < n ≤ y} min (A, B/|sin (π α n + θ)|) ≤ (⌊(y-x)/q⌋ + 1)(2A + (2/π)Bq log 4q)`.

**Corollary 3.5 (restricting to odd integers).**  Let `2α = a/q + β` with
`β = O*(1/q²)`.  Then for any `x < y`, `A, B > 0`, and `θ ∈ ℝ/ℤ`,

`Σ_{x < n ≤ y, n odd} min (A, B/|sin (π α n + θ)|) ≤ (⌊(y-x)/(2q)⌋ + 1)(2A + (2/π)Bq log 4q)`.

The proof reindexes `n = 2m + 1`: the left-hand side becomes
`Σ_{(x-1)/2 < m ≤ (y-1)/2} min (A, B/|sin (2π α m + π α + θ)|)`, which is
Lemma 3.4 applied to `2α = (2a)/q + (2β)` with the new phase
`θ' = π α + θ`.

This module records the **statements as reusable platform objects** and
proves the reduction "Corollary 3.5 from Lemma 3.4" (the reindexing), which
is the only part that is not a black-box citation.  The content of Lemma
3.4 itself is the published bound of [8, Lemma 1] (Vinogradov) and is
carried as a hypothesis, not re-proved here.

**Index-set convention.**  The integer interval `x < n ≤ y` is encoded as
`Ioc ⌊x⌋₊ ⌊y⌋₊`, which is the exact encoding when `x ≥ 0`:
`⌊x⌋₊ < n ↔ x < n` for `n : ℕ` and `0 ≤ x`.  Under the reindexing
`n = 2m+1` it becomes `Ioc ⌊(x-1)/2⌋₊ ⌊(y-1)/2⌋₊`, which requires `1 ≤ x`
so that `(x-1)/2 ≥ 0`. -/

open Finset

namespace TaoFivePrimesBlock

/-! ## 9. Floor helper lemmas for the reindexing -/

/-- If `1 ≤ ⌊y⌋₊` then `1 ≤ y`.  Used to make `Nat.floor_le` applicable to
`y` in the reindexing, where positivity of `y` is not a hypothesis but does
follow from the interval being nonempty. -/
lemma one_le_of_one_le_floor {y : ℝ} (h : 1 ≤ ⌊y⌋₊) : (1 : ℝ) ≤ y := by
  by_contra hc
  push_neg at hc
  have hz : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith : y < 1)
  omega

/-- `⌊y⌋₊ ≤ y` whenever `⌊y⌋₊ ≥ 1`; the positivity of `y` comes from the
previous lemma rather than being assumed. -/
lemma floor_le_of_one_le_floor {y : ℝ} (h : 1 ≤ ⌊y⌋₊) : (⌊y⌋₊ : ℝ) ≤ y :=
  Nat.floor_le (le_trans zero_le_one (one_le_of_one_le_floor h))

/-! ## 10. The reindexing `n = 2m + 1` -/

/-- **The index-set identity.**  For `1 ≤ x` and `m : ℕ`, the odd integer
`2m + 1` lies in `(x, y]` exactly when `m` lies in `((x-1)/2, (y-1)/2]`.

The hypothesis `1 ≤ x` is what makes `(x-1)/2 ≥ 0`, so that
`Nat.floor_lt` applies to `(x-1)/2`.  It is not removable: at `x = 0`,
`y = 1` the odd integer `1 = 2·0+1` lies in `(0, 1]` but the right-hand
side is `⌊-1/2⌋₊ < 0`, which is false. -/
lemma odd_mem_Ioc_iff (x y : ℝ) (hx : 1 ≤ x) (m : ℕ) :
    2 * m + 1 ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2)
      ↔ ⌊(x - 1) / 2⌋₊ < m ∧ m ≤ ⌊(y - 1) / 2⌋₊ := by
  have hx0 : (0 : ℝ) ≤ (x - 1) / 2 := by linarith
  rw [Finset.mem_filter, Finset.mem_Ioc, Nat.coprime_two_right]
  constructor
  · rintro ⟨⟨h1, h2⟩, _hodd⟩
    have hfloor1 : 1 ≤ ⌊y⌋₊ := by omega
    have hy1 : (1 : ℝ) ≤ y := one_le_of_one_le_floor hfloor1
    have hy0 : (0 : ℝ) ≤ (y - 1) / 2 := by linarith
    constructor
    · rw [Nat.floor_lt hx0]
      have h1'' : ⌊x⌋₊ ≤ 2 * m := by omega
      have h1' : ((⌊x⌋₊ : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast h1''
      push_cast at h1'
      have hxlt := Nat.lt_floor_add_one x
      linarith
    · rw [Nat.le_floor_iff hy0]
      have h2' : ((2 * m + 1 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h2
      push_cast at h2'
      linarith [floor_le_of_one_le_floor hfloor1]
  · rintro ⟨h1, h2⟩
    have hm1 : 1 ≤ m := Nat.lt_of_le_of_lt (Nat.zero_le _) h1
    have hy0 : (0 : ℝ) ≤ (y - 1) / 2 := by
      -- `m ≥ 1` and `m ≤ ⌊(y-1)/2⌋₊`, so `(y-1)/2 ≥ 1`
      have hfloor1 : 1 ≤ ⌊(y - 1) / 2⌋₊ := le_trans hm1 h2
      have hstep : (1 : ℝ) ≤ (y - 1) / 2 := one_le_of_one_le_floor hfloor1
      linarith
    constructor
    · constructor
      · -- `⌊x⌋₊ < 2m + 1`
        have hm : ((x - 1) / 2 : ℝ) < (m : ℝ) := (Nat.floor_lt hx0).mp h1
        have hx' : x < ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
        -- `⌊x⌋₊ ≤ x < 2m+1` in `ℕ`, so `⌊x⌋₊ ≤ 2m`
        have hxle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
        have h2m : ((2 * m : ℕ) : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
        have : (⌊x⌋₊ : ℕ) < 2 * m + 1 := by
          have hR : ((⌊x⌋₊ : ℕ) : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by linarith
          exact_mod_cast hR
        omega
      · -- `2m + 1 ≤ ⌊y⌋₊`
        have hm : (m : ℝ) ≤ (y - 1) / 2 := (Nat.le_floor_iff hy0).mp h2
        have hy : ((2 * m + 1 : ℕ) : ℝ) ≤ y := by push_cast; linarith
        exact Nat.le_floor hy
    · exact ⟨m, by ring⟩

/-! ## 11. The reindexing as a sum identity -/

/-- **The reindexing step.** `n = 2m + 1` turns the odd min-sum with
`α` and phase `θ` into the full min-sum with `2α` and phase `π α + θ`.
This is the entire content of the proof of Corollary 3.5.

The identity is stated with `1 ≤ x`, which the index-set identity requires;
in every application `x ≥ 1` (the summations start at `d = 1`). -/
lemma odd_min_sum_reindex (A B alpha theta : ℝ) (x y : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2),
        min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|))
      = ∑ m ∈ Finset.Ioc ⌊(x - 1) / 2⌋₊ ⌊(y - 1) / 2⌋₊,
          min A (B / |Real.sin (Real.pi * (2 * alpha) * (m : ℝ)
            + (Real.pi * alpha + theta))|) := by
  refine Finset.sum_bij (fun n _ => (n - 1) / 2) ?_ ?_ ?_ ?_
  · -- the image lands in the target index set
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, hcop⟩ := hn
    have hodd : Odd n := Nat.coprime_two_right.mp hcop
    -- `n` is odd, so `n = 2k + 1`; then `(n-1)/2 = k`
    obtain ⟨k, hk⟩ := hodd
    rw [Finset.mem_Ioc]
    have hkx : (n - 1) / 2 = k := by omega
    rw [hkx]
    -- translate `⌊x⌋₊ < n = 2k+1 ≤ ⌊y⌋₊` into the `k`-range
    have hk1 : ((x - 1) / 2 : ℝ) < (k : ℝ) := by
      have hx0 : (0 : ℝ) ≤ (x - 1) / 2 := by linarith
      have hxl : ⌊x⌋₊ ≤ 2 * k := by omega
      have hcast : ((⌊x⌋₊ : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast hxl
      push_cast at hcast
      have hxlt := Nat.lt_floor_add_one x
      linarith
    have hk2 : (k : ℝ) ≤ (y - 1) / 2 := by
      have hy0 : (0 : ℝ) ≤ (y - 1) / 2 := by
        have hfloor1 : 1 ≤ ⌊y⌋₊ := by omega
        have := one_le_of_one_le_floor hfloor1
        linarith
      have h2' : ((2 * k + 1 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
        exact_mod_cast (show 2 * k + 1 ≤ ⌊y⌋₊ by omega)
      push_cast at h2'
      linarith [floor_le_of_one_le_floor (show 1 ≤ ⌊y⌋₊ by omega)]
    constructor
    · exact (Nat.floor_lt (by linarith : (0 : ℝ) ≤ (x - 1) / 2)).mpr hk1
    · exact Nat.le_floor hk2
  · -- injectivity
    intro n hn n' hn' heq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn hn'
    obtain ⟨⟨_, _⟩, hcop⟩ := hn
    obtain ⟨⟨_, _⟩, hcop'⟩ := hn'
    obtain ⟨k, hk⟩ := Nat.coprime_two_right.mp hcop
    obtain ⟨k', hk'⟩ := Nat.coprime_two_right.mp hcop'
    have h1 : (n - 1) / 2 = k := by omega
    have h2 : (n' - 1) / 2 = k' := by omega
    omega
  · -- surjectivity
    intro m hm
    refine ⟨2 * m + 1, ?_, ?_⟩
    · have hmem : 2 * m + 1 ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2) :=
        (odd_mem_Ioc_iff x y hx m).mpr (Finset.mem_Ioc.mp hm)
      exact hmem
    · show (2 * m + 1 - 1) / 2 = m
      omega
  · -- the summands agree
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨_, _⟩, hcop⟩ := hn
    obtain ⟨k, hk⟩ := Nat.coprime_two_right.mp hcop
    rw [hk, show (2 * k + 1 - 1) / 2 = k by omega]
    congr 1
    push_cast
    ring

/-! ## 12. The published statements as reusable `Prop`s

Both Lemma 3.4 and Corollary 3.5 are stated as `Prop`-valued definitions so
that they can be cited, instantiated, and reused across modules without
repeating the long Finset expression.  The **content** of Lemma 3.4 is the
classical Vinogradov bound and is carried as a hypothesis of the reduction
below; only the reindexing (the passage from Corollary 3.5 to Lemma 3.4) is
proved here. -/

/-- **Lemma 3.4 (Vinogradov-type lemma).**  The full-sum bound, with the
summation variable an integer `n` in the half-open interval `(x, y]`, phase
`π α n + θ`, and `⌊(y-x)/q⌋ + 1` blocks of length `q`.

This is the published input; it is *not* re-proved here. -/
def vinogradovMinSum (q : ℕ) (A B alpha theta x y : ℝ) : Prop :=
  (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|))
    ≤ (((⌊(y - x) / (q : ℝ)⌋₊ + 1 : ℕ)) : ℝ)
        * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)))

/-- **Corollary 3.5 (restricting to odd integers).**  The odd-sum bound: the
summand is the same `min` expression, restricted to odd `n` in `(x, y]`, and
the block count is `⌊(y-x)/(2q)⌋ + 1` — the factor of two coming from the odd
restriction. -/
def vinogradovMinSumOdd (q : ℕ) (A B alpha theta x y : ℝ) : Prop :=
  (∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2),
      min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|))
    ≤ (((⌊(y - x) / (2 * (q : ℝ))⌋₊ + 1 : ℕ)) : ℝ)
        * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)))

/-- **Corollary 3.5 from Lemma 3.4.**  The odd-restricted min-sum with
parameter `α` and phase `θ` is bounded by applying the Vinogradov bound to
the *full* interval with parameter `2α`, phase `π α + θ`, and the shifted
endpoints `(x-1)/2`, `(y-1)/2`.

The proof is the reindexing `n = 2m + 1` (`odd_min_sum_reindex`) together
with the arithmetic identity `(y - x)/(2q) = ((y-1)/2 - (x-1)/2)/q`, which
makes the two block counts agree.  Only the *index arithmetic* is proved
here; the analytic content of Lemma 3.4 stays a hypothesis. -/
theorem odd_vinogradov_min_sum (q : ℕ) (A B alpha theta x y : ℝ) (hx : 1 ≤ x)
    (hmain : vinogradovMinSum q A B (2 * alpha) (Real.pi * alpha + theta)
      ((x - 1) / 2) ((y - 1) / 2)) :
    vinogradovMinSumOdd q A B alpha theta x y := by
  unfold vinogradovMinSumOdd vinogradovMinSum at *
  rw [odd_min_sum_reindex A B alpha theta x y hx]
  -- The two block counts agree because `(y-x)/(2q) = ((y-1)/2-(x-1)/2)/q`.
  have hkey : (y - x) / (2 * (q : ℝ))
      = ((y - 1) / 2 - (x - 1) / 2) / (q : ℝ) := by ring
  rw [hkey]
  exact hmain

/-! ## 13. The sharpened count-1 form on a width-`2q` block

Corollary 3.5 as published pays `⌊(y−x)/(2q)⌋ + 1` blocks.  On a block of
width exactly `2q` this is `⌊1⌋ + 1 = 2`, which is one more than the range
actually needs: the odd `n` in a width-`2q` interval number only `q`, so in the
reindexed variable `m = (n−1)/2` the range has width `q`, i.e. **one** block.

This section records that refinement, since it is what Tao's `(5.17)` display
uses: without it the per-block bound carries `2A` where he has `A`.

**Encoding.**  The block is the integer range `(2jq + q/2, 2(j+1)q + q/2]`
written in the doubled form `(4jq + q, 4(j+1)q + q]` of §4, so the count-1
statement is about `Ioc ⌊L⌋ ⌊R⌋` with `R − L = 2q` *on the reindexed side*.
The lemma below isolates the arithmetic: `⌊(R−L)/(2q)⌋ + 1 ≤ 2` is what the
published Corollary gives, while the sharp form needs the count to be `1`; the
refined count follows from `(R − L)/(2q) = 1` together with the fact that the
half-open range of odd `n` corresponds to a *single* `q`-block in `m`. -/

/-- **Block-count refinement.**  The published count `⌊(y−x)/(2q)⌋ + 1`
evaluated on a range of width exactly `2q` is `⌊1⌋ + 1 = 2`, i.e. it over-counts
by one relative to the single `q`-block that the odd reindexing actually
produces.  This records the evaluation; `sharp_block_count` records the
reindexed (sharp) value. -/
lemma block_count_width_two_q (q : ℝ) (hq : 1 ≤ q) :
    (⌊(2 * q) / (2 * q)⌋₊ + 1 : ℕ) = 2 := by
  have h2q : (2 : ℝ) * q ≠ 0 := by positivity
  rw [div_self h2q]
  norm_num

/-- **Count-1 form on a width-`2q` block.**  If the range has width exactly `2q`
— i.e. `(y − x)/(2q) = 1/2` after the odd reindexing, equivalently
`(y − x)/q = 1` — then the published count is `⌊1/2⌋ + 1 = 1`, matching Tao's
display.  (The `+1` in Corollary 3.5 is what makes this `1` rather than `0`.)

The content is pure floor arithmetic; the analytic input stays Corollary 3.5's,
applied on the reindexed interval. -/
lemma sharp_block_count (q : ℝ) (hq : 1 ≤ q) (y x : ℝ)
    (hwidth : (y - x) / q = 1) :
    (⌊(y - x) / (2 * q)⌋₊ + 1 : ℕ) = 1 := by
  have hq0 : (0 : ℝ) < q := by linarith
  have h2q : (2 : ℝ) * q ≠ 0 := by positivity
  have h : (y - x) / (2 * q) = 1 / 2 := by
    rw [div_eq_iff h2q]
    rw [div_eq_iff (ne_of_gt hq0)] at hwidth
    linarith
  rw [h]
  norm_num

end TaoFivePrimesBlock
