import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option maxHeartbeats 800000
set_option autoImplicit false

open Finset

/-! # The Vinogradov estimate on integer intervals, and the odd reflection

Tao, *Every odd number greater than 1 is the sum of at most five primes*,
arXiv:1201.6656v4, Lemma 3.4 and Corollary 3.5.

Tao states both results for **integer** summation ranges:

> **Lemma 3.4.** Let `α = a/q + β` with `β = O*(1/q²)`. Then for any `x < y`,
> `A, B > 0` and `θ`,  `Σ_{x<n≤y} min(A, B/|sin(παn+θ)|) ≤ (⌊(y-x)/q⌋+1)(2A + (2/π)Bq log 4q)`.
>
> *Proof.* "By subdivision of the interval `[x,y]` it suffices to show
> `Σ_{x<n≤x+q} min(A, 1/|sin(παn+θ)|) ≤ 2A + (2/π)q log 4q` for all `x`."

The **per-block** inequality displayed in that proof is the actual content;
the `⌊(y-x)/q⌋ + 1` count is what subdivision of the range into `⌈(y-x)/q⌉`
blocks of length `q` gives.  Both applications inside Tao's Section 5.2 use
exactly one block, and there the published count over-counts by one
(`⌊1⌋ + 1 = 2` where one block suffices), which is worth a factor of two in
`(5.17)`.  So this module records the estimate in the **single-block form**,
which is what the source actually proves, and derives the odd form and the
reflection bound from it.

Two pieces of genuinely new content are proved here:

* `odd_sum_reindex` — the reindexing `n = 2m + 1` of Corollary 3.5, over `ℤ`
  (where it is exact; over `ℕ` the `Nat.floor` clamping at `0` forces a
  spurious hypothesis `1 ≤ x` and, worse, makes the reflection below
  inexpressible);
* `odd_symm_sum` — the reflection `z ↦ -z`, which halves the one-sided odd
  sum.  Tao uses it implicitly in Section 5.2 ("by symmetry we may thus bound
  the contribution of the `d ≤ q/2` terms ... by `2 log 2 log 2x((2/π)q log 4q + 4q)`"),
  halving the `4q + (2/π)q log 4q` of Corollary 3.5.  The halving is not
  optional: without it the assembled `(5.17)` exceeds the platform's right-hand
  side by a factor `1.29` in the worst admissible corner.

The analytic content of Lemma 3.4 (Vinogradov's lemma, cited by Tao from
[8, Lemma 1]) is *not* re-proved; `vinogradovBlock` carries it as a
`Prop`-valued hypothesis. -/

namespace TaoFivePrimesVinogradov

/-! ## 1. Half-open integer intervals -/

/-- The integers `z` with `x < z ≤ y`, as a `Finset ℤ`. -/
noncomputable def zIoc (x y : ℝ) : Finset ℤ := Finset.Icc (⌊x⌋ + 1) ⌊y⌋

lemma mem_zIoc {x y : ℝ} {z : ℤ} : z ∈ zIoc x y ↔ x < (z : ℝ) ∧ (z : ℝ) ≤ y := by
  unfold zIoc
  rw [Finset.mem_Icc]
  constructor
  · intro h
    have hlt : ⌊x⌋ < z := by omega
    exact ⟨(Int.floor_lt).mp hlt, (Int.le_floor).mp h.2⟩
  · intro h
    constructor
    · have : ⌊x⌋ < z := (Int.floor_lt).mpr h.1
      omega
    · exact (Int.le_floor).mpr h.2

/-! ## 2. The reindexing `n = 2m + 1` -/

/-- An odd integer `2m + 1` lies in `(x, y]` exactly when `m` lies in
`((x-1)/2, (y-1)/2]`.  Over `ℤ` this is exact — no side condition — because
`Int.floor` is not clamped at zero. -/
lemma odd_mem_zIoc_iff (x y : ℝ) (m : ℤ) :
    (2 * m + 1 : ℤ) ∈ zIoc x y ↔ m ∈ zIoc ((x - 1) / 2) ((y - 1) / 2) := by
  rw [mem_zIoc, mem_zIoc]
  constructor
  · intro h
    push_cast at h
    constructor <;> nlinarith [h.1, h.2]
  · intro h
    push_cast at h ⊢
    constructor <;> nlinarith [h.1, h.2]

/-- For odd `z`, halving is exact: `2 * ((z-1)/2) + 1 = z`. -/
lemma two_mul_div_two_add_one (z : ℤ) (h : Odd z) : 2 * ((z - 1) / 2) + 1 = z := by
  obtain ⟨k, rfl⟩ := h
  omega

/-- **The reindexing.**  Summation over the odd integers of `(x, y]` equals
summation over all integers of `((x-1)/2, (y-1)/2]` with `m ↦ 2m+1`. -/
lemma odd_sum_reindex (f : ℤ → ℝ) (x y : ℝ) :
    (∑ z ∈ (zIoc x y).filter (fun z => Odd z), f z)
      = ∑ m ∈ zIoc ((x - 1) / 2) ((y - 1) / 2), f (2 * m + 1) := by
  refine Finset.sum_bij (fun z _ => (z - 1) / 2) ?hmem ?hinj ?hsurj ?hval
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzxy, hodd⟩ := hz
    obtain ⟨k, hk⟩ := hodd
    have hk' : (z - 1) / 2 = k := by omega
    rw [hk']
    exact (odd_mem_zIoc_iff x y k).mp (by simpa [hk] using hzxy)
  · intro z hz z' hz' heq
    rw [Finset.mem_filter] at hz hz'
    have hzodd : Odd z := hz.2
    have hzodd' : Odd z' := hz'.2
    have h1 := two_mul_div_two_add_one z hzodd
    have h2 := two_mul_div_two_add_one z' hzodd'
    omega
  · intro m hm
    refine ⟨2 * m + 1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨(odd_mem_zIoc_iff x y m).mpr hm, ⟨m, rfl⟩⟩
    · omega
  · intro z hz
    rw [Finset.mem_filter] at hz
    congr 1
    exact (two_mul_div_two_add_one z hz.2).symm

/-! ## 3. The two estimates

Both are recorded as `Prop`-valued definitions so they can be cited,
instantiated and reused.  The `width` condition is an implication inside the
`Prop` so that instantiations need not supply it eagerly. -/

/-- **Lemma 3.4, single-block form.**  On an integer range of width at most
`q`, the Vinogradov min-sum is at most `2A + (2/π) B q log 4q`.

This is the inequality Tao's proof of Lemma 3.4 reduces to ("by subdivision of
the interval it suffices to show ... for all `x`"); the classical content is
Vinogradov's lemma and is carried as a hypothesis here. -/
def vinogradovBlock (q : ℕ) (A B alpha theta x y : ℝ) : Prop :=
  y ≤ x + (q : ℝ) →
    (∑ z ∈ zIoc x y, min A (B / |Real.sin (Real.pi * alpha * (z : ℝ) + theta)|))
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ))

/-- **Corollary 3.5, single-block form.**  The same bound for the *odd*
integers of a range of width at most `2q` — the factor of two coming from the
odd restriction. -/
def vinogradovBlockOdd (q : ℕ) (A B alpha theta x y : ℝ) : Prop :=
  y ≤ x + 2 * (q : ℝ) →
    (∑ z ∈ (zIoc x y).filter (fun z => Odd z),
        min A (B / |Real.sin (Real.pi * alpha * (z : ℝ) + theta)|))
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ))

/-- **Corollary 3.5 from Lemma 3.4.**  The odd min-sum with parameter `α` and
phase `θ` is the full min-sum with parameter `2α`, phase `πα + θ`, on the
shifted endpoints `((x-1)/2, (y-1)/2]`.  The width halves, which is exactly why
the admissible width doubles. -/
theorem odd_vinogradov_block (q : ℕ) (A B alpha theta x y : ℝ)
    (hmain : vinogradovBlock q A B (2 * alpha) (Real.pi * alpha + theta)
      ((x - 1) / 2) ((y - 1) / 2)) :
    vinogradovBlockOdd q A B alpha theta x y := by
  intro hwidth
  unfold vinogradovBlock at hmain
  rw [odd_sum_reindex]
  refine le_trans (le_of_eq ?_) (hmain ?_)
  · apply Finset.sum_congr rfl
    intro m hm
    congr 3
    have : Real.pi * alpha * ((2 * m + 1 : ℤ) : ℝ) + theta
        = Real.pi * (2 * alpha) * (m : ℝ) + (Real.pi * alpha + theta) := by
      push_cast
      ring
    rw [this]
  · nlinarith

/-! ## 4. The reflection `z ↦ -z`

Tao's small-`d` range is `d ≤ q/2`; Corollary 3.5 on the *symmetric* range
`|z| ≤ q/2` costs `2A + (2/π)Bq log 4q`, and the one-sided sum is exactly half
of that.  This section proves the halving. -/

/-- Odd integers pair up under `z ↦ -z`. -/
lemma odd_neg (z : ℤ) (h : Odd z) : Odd (-z) := by
  obtain ⟨k, rfl⟩ := h
  use -k - 1
  ring

/-- `0` is not odd. -/
lemma not_odd_zero : ¬ Odd (0 : ℤ) := by
  rintro ⟨k, hk⟩
  omega

/-- **Reflection.**  For an even summand `g`, the odd sum over `[-N, N]` is
twice the odd sum over `[1, N]`. -/
lemma odd_symm_sum (g : ℤ → ℝ) (hg : ∀ z : ℤ, g (-z) = g z) (N : ℤ) :
    (∑ z ∈ (Finset.Icc (-N) N).filter (fun z => Odd z), g z)
      = 2 * (∑ z ∈ (Finset.Icc (1 : ℤ) N).filter (fun z => Odd z), g z) := by
  let A : Finset ℤ := (Finset.Icc (-N) N).filter (fun z => Odd z)
  let B : Finset ℤ := (Finset.Icc (1 : ℤ) N).filter (fun z => Odd z)
  let C : Finset ℤ := (Finset.Icc (-N) (-1)).filter (fun z => Odd z)
  have hdisj : Disjoint C B := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [Finset.mem_filter, Finset.mem_Icc] at hz hz'
    omega
  have hunion : C ∪ B = A := by
    ext z
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro (⟨⟨h1, h2⟩, ho⟩ | ⟨⟨h1, h2⟩, ho⟩)
      · exact ⟨⟨h1, by omega⟩, ho⟩
      · exact ⟨⟨by omega, h2⟩, ho⟩
    · rintro ⟨⟨h1, h2⟩, ho⟩
      by_cases hz : z ≤ -1
      · left
        exact ⟨⟨h1, hz⟩, ho⟩
      · right
        have hz1 : (1 : ℤ) ≤ z := by
          obtain ⟨k, hk⟩ := ho
          have hz0 : z ≠ 0 := by omega
          omega
        exact ⟨⟨hz1, h2⟩, ho⟩
  have hCB : (∑ z ∈ C, g z) = ∑ z ∈ B, g z := by
    refine Finset.sum_bij (fun z _ => -z) ?hmem ?hinj ?hsurj ?hval
    · intro z hz
      rw [Finset.mem_filter, Finset.mem_Icc] at hz
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, odd_neg z hz.2⟩
    · intro z hz z' hz' heq
      omega
    · intro b hb
      rw [Finset.mem_filter, Finset.mem_Icc] at hb
      refine ⟨-b, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, by omega⟩, odd_neg b hb.2⟩
      · ring
    · intro z hz
      rw [Finset.mem_filter] at hz
      simpa using (hg (-z))
  calc
    (∑ z ∈ (Finset.Icc (-N) N).filter (fun z => Odd z), g z)
        = ∑ z ∈ A, g z := rfl
    _ = ∑ z ∈ C ∪ B, g z := by rw [hunion]
    _ = (∑ z ∈ C, g z) + ∑ z ∈ B, g z := by rw [Finset.sum_union hdisj]
    _ = 2 * (∑ z ∈ B, g z) := by rw [hCB]; ring
    _ = 2 * (∑ z ∈ (Finset.Icc (1 : ℤ) N).filter (fun z => Odd z), g z) := rfl

/-- `zIoc (-(M:ℝ) - 1) (M:ℝ)` is exactly the symmetric integer interval
`[-M, M]`. -/
lemma zIoc_neg_sub_one (M : ℤ) : zIoc (-(M : ℝ) - 1) (M : ℝ) = Finset.Icc (-M) M := by
  unfold zIoc
  ext z
  rw [show ⌊-(M : ℝ) - 1⌋ = -M - 1 by
        rw [show -(M : ℝ) - 1 = ((-M - 1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast],
      show ⌊(M : ℝ)⌋ = M by exact Int.floor_intCast M]
  simp only [Finset.mem_Icc]
  omega

/-- **The halved one-sided bound.**  With the phase `θ = 0` the summand
`min(A, B/|sin(παz)|)` is even in `z`, so the one-sided odd sum over
`[1, M]` is at most `A + (1/π) B q log 4q`, half of Corollary 3.5's
`2A + (2/π) B q log 4q`, provided `2M + 1 ≤ 2q`.

This is the statement Tao invokes with `A = 2q`, `B = 1`, `M = ⌊q/2⌋`, giving
`2q + (1/π) q log 4q`. -/
lemma odd_symm_min_sum_le (q : ℕ) (A B alpha : ℝ) (M : ℤ)
    (hwidth : 2 * (M : ℝ) + 1 ≤ 2 * (q : ℝ))
    (hv : vinogradovBlockOdd q A B alpha 0 (-(M : ℝ) - 1) (M : ℝ)) :
    (∑ z ∈ (Finset.Icc (1 : ℤ) M).filter (fun z => Odd z),
        min A (B / |Real.sin (Real.pi * alpha * (z : ℝ))|))
      ≤ A + (1 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
  have htwo : (∑ z ∈ (Finset.Icc (-M) M).filter (fun z => Odd z),
        min A (B / |Real.sin (Real.pi * alpha * (z : ℝ))|))
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
    unfold vinogradovBlockOdd at hv
    simpa [zIoc_neg_sub_one M] using hv (by nlinarith)
  have hsym := odd_symm_sum
    (fun z : ℤ => min A (B / |Real.sin (Real.pi * alpha * (z : ℝ))|))
    (by
      intro z
      have harg : Real.pi * alpha * ((-z : ℤ) : ℝ) = -(Real.pi * alpha * (z : ℝ)) := by
        push_cast
        ring
      rw [harg, Real.sin_neg, abs_neg]) M
  have h2S : 2 * (∑ z ∈ (Finset.Icc (1 : ℤ) M).filter (fun z => Odd z),
        min A (B / |Real.sin (Real.pi * alpha * (z : ℝ))|))
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
    rw [← hsym]
    exact htwo
  have hR : 2 * (A + (1 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)))
      = 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
    ring
  nlinarith

/-! ## 5. Bridging the platform's `ℕ`-valued divisor set

The node sums over `theorem51Divisors U V ⊆ ℕ`; the estimates above live on
`ℤ`.  The bridge is the cast `d ↦ (d : ℤ)`. -/

lemma nat_odd_iff_int_odd (d : ℕ) : Odd (d : ℤ) ↔ Odd d := by
  constructor
  · rintro ⟨k, hk⟩
    have hk0 : 0 ≤ k := by
      by_contra hneg
      have hkneg : k ≤ -1 := by omega
      have : (d : ℤ) ≤ -1 := by nlinarith [show (d : ℤ) = 2 * k + 1 from hk]
      omega
    lift k to ℕ using hk0
    use k
    exact_mod_cast hk
  · rintro ⟨k, hk⟩
    use (k : ℤ)
    exact_mod_cast hk

/-- **Cast bridge.**  A sum over the odd naturals in `[1, N]` is the sum over
the odd integers in `[1, N]`. -/
lemma sum_nat_odd_eq_int_odd (N : ℕ) (f : ℤ → ℝ) :
    (∑ d ∈ (Finset.Icc 1 N).filter (fun d : ℕ => Odd d), f (d : ℤ))
      = ∑ z ∈ (Finset.Icc (1 : ℤ) (N : ℤ)).filter (fun z => Odd z), f z := by
  refine Finset.sum_bij (fun d _ => (d : ℤ)) ?hmem ?hinj ?hsurj ?hval
  · intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by exact_mod_cast hd.1.1, by exact_mod_cast hd.1.2⟩,
           (nat_odd_iff_int_odd d).mpr hd.2⟩
  · intro d hd d' hd' heq
    exact_mod_cast heq
  · intro z hz
    rw [Finset.mem_filter, Finset.mem_Icc] at hz
    have hz0 : 0 ≤ z := by omega
    lift z to ℕ using hz0
    refine ⟨z, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by exact_mod_cast hz.1.1, by exact_mod_cast hz.1.2⟩,
             (nat_odd_iff_int_odd z).mp hz.2⟩
    · rfl
  · intro d hd
    rfl

end TaoFivePrimesVinogradov
