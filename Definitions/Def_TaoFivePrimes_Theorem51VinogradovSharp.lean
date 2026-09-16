import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Finset

/-! # The odd Vinogradov estimate at the sharp block count, and the reflection

Tao, *Every odd number greater than 1 is the sum of at most five primes*,
arXiv:1201.6656v4, Lemma 3.4 and Corollary 3.5.

Tao states both results for **integer** summation ranges:

> **Lemma 3.4.** Let `α = a/q + β` with `β = O*(1/q²)`. Then for any `x < y`,
> `A, B > 0` and `θ`,  `Σ_{x<n≤y} min(A, B/|sin(παn+θ)|) ≤ (⌊(y-x)/q⌋+1)(2A + (2/π)Bq log 4q)`.
>
> *Proof.* "By subdivision of the interval `[x,y]` it suffices to show
> `Σ_{x<n≤x+q} min(A, 1/|sin(παn+θ)|) ≤ 2A + (2/π)q log 4q` for all `x`."
>
> **Corollary 3.5.** Let `2α = a/q + β` with `β = O*(1/q²)`. Then
> `Σ_{x<n≤y} 1_{(n,2)=1} min(A, B/|sin(παn+θ)|) ≤ (⌊(y-x)/(2q)⌋+1)(2A + (2/π)Bq log 4q)`.

Two things about this pair are decisive for Section 5.2 and are the content of
this module.

**(a) The sharp block count is one, not two.**  Corollary 3.5 is quoted in
Section 5.2 on a block `2jq + q/2 < d ≤ 2(j+1)q + q/2`, whose width is exactly
`2q`; the published count `⌊(y-x)/(2q)⌋ + 1` therefore evaluates to `⌊1⌋+1 = 2`.
But the reindexing `d = 2m+1` in the proof of Corollary 3.5 turns the odd `d` of
a range of width `2q` into **all** `m` of a range of width `q`, and Lemma 3.4 is
applied to that range with **one** block.  The covering count
`⌊W/q⌋ + 1` over-counts by one whenever `q ∣ W`, and it is exactly the case
`W = q` that occurs.  So the estimate actually proved is the *single-block* one,
recorded below as `oddBlockBound`; carrying the published count instead doubles
the constant of (5.17) from `0.89` to `1.78`.

**(b) The reflection `z ↦ -z` halves the one-sided odd sum.**  In Section 5.2
Tao obtains `Σ_{d ∈ ℤ, -q/2 ≤ d ≤ q/2} 1_{(d,2)=1} min(2q, 1/|sin(2πdα)|) ≤ (2/π)q log 4q + 4q`
from Corollary 3.5 and then says "by symmetry we may thus bound the
contribution of the `d ≤ q/2` terms by `2 log 2 log 2x ((2/π)q log 4q + 4q)`".
The summand is even in `d`, and the odd integers of `[-M, M]` are exactly the
odd integers of `[1, M]` together with their negatives, so the one-sided sum is
half of the symmetric one.  This halving is **not** optional: it is what turns
the block-count slack `UV/(2q) + 3/4` into Tao's `UV/(2q) + 5/4`, and without
it the assembled bound overshoots the platform's right-hand side by a factor
`1.29` in the worst admissible corner.

The analytic content of Lemma 3.4 (the classical Vinogradov estimate) is *not*
re-proved here; `blockBound` carries it as a `Prop`-valued hypothesis. -/

namespace TaoFivePrimesVinogradovSharp

/-! ## 1. The summand, and its two symmetries -/

/-- The min-sum summand, with the source's convention at the zeros of the sine:
`A` where the sine vanishes (the mathematically correct value of the minimum
there), and `min A (B/|sin|)` elsewhere.  A bare `min` would contribute
`min A (B/0) = 0` at a vanishing phase, because Lean's real division returns
`0` there. -/
noncomputable def vmin (A B alpha theta : ℝ) (n : ℤ) : ℝ :=
  if Real.sin (Real.pi * alpha * (n : ℝ) + theta) = 0 then A
  else min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|)

/-- `vmin` is nonnegative for `A, B ≥ 0`. -/
lemma vmin_nonneg {A B alpha theta : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (n : ℤ) :
    0 ≤ vmin A B alpha theta n := by
  unfold vmin
  split_ifs with h
  · exact hA
  · exact le_min hA (div_nonneg hB (abs_nonneg _))

/-- `vmin` is even in the summation variable when the phase `θ` vanishes. -/
lemma vmin_neg (A B alpha : ℝ) (z : ℤ) :
    vmin A B alpha 0 (-z) = vmin A B alpha 0 z := by
  unfold vmin
  have harg : Real.pi * alpha * ((-z : ℤ) : ℝ) + 0
      = -(Real.pi * alpha * (z : ℝ) + 0) := by
    push_cast
    ring
  have hsin : Real.sin (Real.pi * alpha * ((-z : ℤ) : ℝ) + 0)
      = - Real.sin (Real.pi * alpha * (z : ℝ) + 0) := by
    rw [harg, Real.sin_neg]
  by_cases h : Real.sin (Real.pi * alpha * (z : ℝ) + 0) = 0
  · have h' : Real.sin (Real.pi * alpha * ((-z : ℤ) : ℝ) + 0) = 0 := by
      rw [hsin, h, neg_zero]
    simp [h, h']
  · have h' : Real.sin (Real.pi * alpha * ((-z : ℤ) : ℝ) + 0) ≠ 0 := by
      intro hz
      apply h
      rw [hsin] at hz
      exact neg_eq_zero.mp hz
    simp [h, h', hsin, abs_neg]

/-- **The reindexing `n = 2m+1` at the level of the summand.**  The odd integer
`2m+1` sees the phase `πα(2m+1) + θ = π(2α)m + (πα + θ)`, i.e. the doubled
frequency and a shifted phase. -/
lemma vmin_odd (A B alpha theta : ℝ) (m : ℤ) :
    vmin A B alpha theta (2 * m + 1) = vmin A B (2 * alpha) (Real.pi * alpha + theta) m := by
  unfold vmin
  have harg : Real.pi * alpha * ((2 * m + 1 : ℤ) : ℝ) + theta
      = Real.pi * (2 * alpha) * (m : ℝ) + (Real.pi * alpha + theta) := by
    push_cast
    ring
  rw [harg]

/-! ## 2. Half-open integer intervals and the reindexing -/

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

/-! ## 3. The block estimates at the sharp count

Both are recorded as `Prop`-valued definitions so they can be cited,
instantiated and reused.  The width condition is an implication inside the
`Prop` so that instantiations need not supply it eagerly. -/

/-- Right-hand side common to both estimates. -/
noncomputable def vRhs (q : ℕ) (A B : ℝ) : ℝ :=
  2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ))

/-- **Lemma 3.4, single-block form.**  On an integer range of width at most `q`,
the Vinogradov min-sum is at most `2A + (2/π) B q log 4q`.

This is the inequality Tao's proof of Lemma 3.4 reduces to ("by subdivision of
the interval it suffices to show ... for all `x`"); the classical content is
Vinogradov's lemma and is carried as a hypothesis here. -/
def blockBound (q : ℕ) (A B alpha theta x y : ℝ) : Prop :=
  y ≤ x + (q : ℝ) →
    (∑ n ∈ zIoc x y, vmin A B alpha theta n) ≤ vRhs q A B

/-- **Corollary 3.5, single-block form.**  The same bound for the *odd*
integers of a range of width at most `2q` — the factor of two in the admissible
width coming from the odd restriction, and the block count being **one**. -/
def oddBlockBound (q : ℕ) (A B alpha theta x y : ℝ) : Prop :=
  y ≤ x + 2 * (q : ℝ) →
    (∑ z ∈ (zIoc x y).filter (fun z => Odd z), vmin A B alpha theta z) ≤ vRhs q A B

/-- **Feeding the platform's block estimate into `blockBound`.**  The platform
states the block estimate on `Finset.Ioc m (m + q)` for integer `m`; `zIoc x y`
is contained in `Finset.Ioc ⌊x⌋ (⌊x⌋ + q)` as soon as `y ≤ x + q`, and the
summand is nonnegative, so the sum over the smaller set is no larger. -/
lemma blockBound_of_int_block (q : ℕ) (A B alpha theta x y : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ m : ℤ, (∑ n ∈ Finset.Ioc m (m + (q : ℤ)), vmin A B alpha theta n) ≤ vRhs q A B) :
    blockBound q A B alpha theta x y := by
  intro hwidth
  have hsub : zIoc x y ⊆ Finset.Ioc ⌊x⌋ (⌊x⌋ + (q : ℤ)) := by
    intro z hz
    rw [mem_zIoc] at hz
    rw [Finset.mem_Ioc]
    constructor
    · exact (Int.floor_lt).mpr hz.1
    · have : ((z - (q : ℤ) : ℤ) : ℝ) ≤ x := by
        push_cast
        nlinarith [hz.2, hwidth]
      have h1 : z - (q : ℤ) ≤ ⌊x⌋ := (Int.le_floor).mpr this
      omega
  exact le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro z hzbig hzsmall
      exact vmin_nonneg hA hB z))
    (h ⌊x⌋)

/-- **Corollary 3.5 from Lemma 3.4, at the sharp block count.**  The odd
min-sum with parameter `α` and phase `θ` is the full min-sum with parameter
`2α`, phase `πα + θ`, on the shifted endpoints `((x-1)/2, (y-1)/2]`.  The
width halves, which is exactly why the admissible width doubles — and why the
block count stays `1` rather than becoming `2`. -/
theorem odd_block_from_block (q : ℕ) (A B alpha theta x y : ℝ)
    (hmain : blockBound q A B (2 * alpha) (Real.pi * alpha + theta)
      ((x - 1) / 2) ((y - 1) / 2)) :
    oddBlockBound q A B alpha theta x y := by
  intro hwidth
  unfold blockBound at hmain
  rw [odd_sum_reindex]
  refine le_trans (le_of_eq ?_) (hmain ?_)
  · apply Finset.sum_congr rfl
    intro m hm
    exact vmin_odd A B alpha theta m
  · nlinarith

/-! ## 4. The reflection `z ↦ -z` -/

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

/-- **The halved one-sided bound.**  With the phase `θ = 0` the summand is even
in `z`, so the one-sided odd sum over `[1, M]` is at most
`A + (1/π) B q log 4q`, half of `2A + (2/π) B q log 4q`, provided
`2M + 1 ≤ 2q`.

This is the statement Tao invokes with `A = 2q`, `B = 1`, `M = ⌊q/2⌋`, giving
`2q + (1/π) q log 4q`. -/
lemma odd_symm_min_sum_le (q : ℕ) (A B alpha : ℝ) (M : ℤ)
    (hwidth : 2 * (M : ℝ) + 1 ≤ 2 * (q : ℝ))
    (hv : oddBlockBound q A B alpha 0 (-(M : ℝ) - 1) (M : ℝ)) :
    (∑ z ∈ (Finset.Icc (1 : ℤ) M).filter (fun z => Odd z), vmin A B alpha 0 z)
      ≤ A + (1 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
  have hw : (M : ℝ) ≤ (-(M : ℝ) - 1) + 2 * (q : ℝ) := by
    nlinarith [hwidth]
  have htwo : (∑ z ∈ (Finset.Icc (-M) M).filter (fun z => Odd z), vmin A B alpha 0 z)
      ≤ vRhs q A B := by
    simpa [oddBlockBound, zIoc_neg_sub_one M] using (hv hw)
  have hsym := odd_symm_sum (fun z : ℤ => vmin A B alpha 0 z) (vmin_neg A B alpha) M
  have h2S : 2 * (∑ z ∈ (Finset.Icc (1 : ℤ) M).filter (fun z => Odd z), vmin A B alpha 0 z)
      ≤ vRhs q A B := by
    rw [← hsym]
    exact htwo
  have hR : 2 * (A + (1 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)))
      = vRhs q A B := by
    unfold vRhs
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

/-! ## 6. Instantiation to the per-block hypothesis `hblock`

`examples/five-primes/Theorem51Assembly.lean` §10 consumes, as an explicit
unproved hypothesis named `hblock`, the per-block bound

  `b ≤ X + 2C + (2/π) C q log 4q`,  `X = (1/2)(x/L) log x`,  `C = 4 (log 2) log 2x`,

and its docstring records that `hblock` *is* Corollary 3.5 at the sharp count,
with `A` set to the frozen `x`-term and `C` added back once per `d`.

The lemmas below make that identification literal rather than rhetorical: with
`A = X/2 + C` and `B = C`, the sharpened estimate's right-hand side `vRhs` is
*definitionally* the §10 right-hand side.  Nothing analytic is added — the point
is that a caller holding `oddBlockBound` can close `hblock` by a rewrite, so
`hblock` drops off the assembly's list of hypotheses. -/

/-- **The two right-hand sides agree.**  With `A = X/2 + C`, `B = C`, the
sharpened Corollary 3.5 right-hand side `vRhs q A B = 2A + (2/π) B q log 4q`
equals the `Theorem51Assembly` §10 right-hand side
`X + 2C + (2/π) C q log 4q`. -/
lemma vRhs_eq_hblock_rhs (q : ℕ) (X C : ℝ) :
    vRhs q (X / 2 + C) C
      = X + 2 * C + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
  unfold vRhs
  ring

/-- **`hblock` from the sharpened estimate.**  A caller holding the sharpened
bound with `A = X/2 + C`, `B = C` obtains the §10 form with `X` and `C`.  The
sum is abstracted as `b` because identifying it with the frozen envelope sum
over the block's odd `d` is the analytic step performed in §10 itself, not
here. -/
lemma hblock_of_sharp (q : ℕ) (X C b : ℝ)
    (hsharp : b ≤ vRhs q (X / 2 + C) C) :
    b ≤ X + 2 * C + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
  rw [← vRhs_eq_hblock_rhs q X C]
  exact hsharp

/-- **The `n`-indexed form of §10.**  `block_sum_envelope_le` folds the actual
odd count `n` into the `C`-budget; the sharpened estimate already pays the
`q/2 + O(1)` count through Corollary 3.5's `+4q` slack, so the two forms are
interchangeable.  Recorded so the instantiation matches §10 verbatim. -/
lemma hblock_n_indexed_of_sharp (q : ℕ) (X C b n : ℝ)
    (hsharp : b + n * C ≤ vRhs q (X / 2 + C) C) :
    b + n * C ≤ X + 2 * C + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
  rw [← vRhs_eq_hblock_rhs q X C]
  exact hsharp

/-- **The `A`-slot is the frozen first alternative plus the constant.**  This
is the arithmetic behind `2 (X/2 + C) = X + 2C`, recorded separately so that the
identification above is not the only evidence the `A`-slot is used correctly. -/
lemma two_A_slot (X C : ℝ) : 2 * (X / 2 + C) = X + 2 * C := by ring

/-- **The `A`-slot is nonnegative** in the regime the assembly uses, where
`C = 4 (log 2) log 2x` and `X > 0`.  This is what licenses applying the
min-sum estimate at `A = X/2 + C`. -/
lemma A_slot_nonneg {x X : ℝ} (hx : 1 ≤ x) (hX : 0 < X) :
    0 ≤ X / 2 + 4 * Real.log 2 * Real.log (2 * x) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by nlinarith)
  nlinarith

/-- **`B`-slot nonnegativity.**  `C = 4 (log 2) log 2x ≥ 0` for `x ≥ 1`, which
is the `B ≥ 0` hypothesis of the min-sum estimate. -/
lemma B_slot_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ 4 * Real.log 2 * Real.log (2 * x) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by nlinarith)
  nlinarith

end TaoFivePrimesVinogradovSharp
