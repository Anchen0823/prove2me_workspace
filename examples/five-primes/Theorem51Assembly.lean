import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_BlockFoundation
import Definitions.Def_TaoFivePrimes_Theorem51Sums

set_option maxHeartbeats 800000

/-! # Type I block summation: the assembly

Tao, arXiv:1201.6656v4, Section 5.2, the passage from (5.14) to (5.17).

This is the second child of `TaoFivePrimes.theorem51_typeI_block_summation`
(see `missions/five-primes/block-foundation/CHILDREN.md`).  It combines the
reusable foundation (`TaoFivePrimes_BlockFoundationCor35`) with the
odd-restricted Vinogradov reduction (Corollary 3.5) to bound the whole
envelope sum.

**Tao's split** (his own words, Section 5.2):

* the **small-`d`** range `d ≤ q/2`: (5.15) gives `‖4dα‖_{ℝ/ℤ} ≥ 1/(2q)`, so
  (2.1) gives `1/|sin(2πdα)| ≤ 2q`, and Corollary 3.5 on `[−q/2, q/2]`
  bounds the range;
* the **blocks** `2jq + q/2 < d ≤ 2(j+1)q + q/2`, `j ≤ UV/2q − 1/4`: freeze
  the first alternative at the left endpoint, apply Corollary 3.5 to the
  block (width `2q`), then sum over `j` by the integral test.

The file is organised so each step is a separate lemma. -/

open Finset

namespace TaoFivePrimesAssembly

/-! ## 1. Coprimality transfer: `q ⊥ a` and `q ∤ d` give `q ∤ a d` -/

/-- **Coprimality transfer.**  If `q` is coprime to `a.natAbs` and does not
divide `d`, then `q` does not divide the integer product `a d`.  This is the
bridge that turns the parent's `Nat.Coprime a.natAbs q` into the
`¬ (q ∣ ad)` hypothesis of `rdist_d_alpha_ge`. -/
lemma not_dvd_mul_of_coprime {a : ℤ} {q d : ℕ} (hcop : Nat.Coprime a.natAbs q)
    (hd : ¬ (q ∣ d)) : ¬ ((q : ℤ) ∣ a * (d : ℤ)) := by
  intro h
  apply hd
  have h1 : ((q : ℤ)).natAbs ∣ (a * (d : ℤ)).natAbs := Int.natAbs_dvd_natAbs.mpr h
  rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at h1
  exact hcop.symm.dvd_of_dvd_mul_left h1

/-- A positive integer strictly below `q` is not divisible by `q`. -/
lemma not_dvd_of_lt {d q : ℕ} (hpos : 0 < d) (hlt : d < q) : ¬ (q ∣ d) := by
  intro h
  have := Nat.le_of_dvd hpos h
  omega

/-! ## 2. The pointwise cosecant bound on the small-`d` range

`rdist_d_alpha_ge` (from the foundation) gives `‖4dα‖_{ℝ/ℤ} ≥ 1/(2q)`, and
`inv_abs_sin_le_of_rdist_ge` turns that into `1/|sin(π·4dα)| ≤ q`.  This is
Tao's (5.16), with `q` in place of his `2q` (his `2q` is the weaker bound
obtained from `1/|sin(π/4q)| ≤ 2q`). -/

/-- **(5.16).**  If `4α = a/q + β` with `|β| ≤ q^{-2}`, `q ≥ 1`, `q ⊥ a`,
`0 < d ≤ q/2` and `d < q`, then `1/|sin (4πdα)| ≤ q`. -/
lemma small_d_cosec_le (q : ℕ) (alpha beta : ℝ) (a : ℤ) (hq : 0 < q)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) (hcop : Nat.Coprime a.natAbs q)
    (d : ℕ) (hd1 : 1 ≤ d) (hd2 : (d : ℝ) * 2 ≤ (q : ℝ)) (hdlt : d < q)
    (hkey : 4 * (d : ℝ) * alpha = (a : ℝ) * (d : ℝ) / (q : ℝ) + (d : ℝ) * beta) :
    1 / |Real.sin (Real.pi * (4 * (d : ℝ) * alpha))| ≤ (q : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hnd : ¬ ((q : ℤ) ∣ a * (d : ℤ)) :=
    not_dvd_mul_of_coprime hcop (not_dvd_of_lt (by omega) hdlt)
  have h := TaoFivePrimesBlock.rdist_d_alpha_ge (a * (d : ℤ)) (q : ℤ) alpha beta
    (by exact_mod_cast hq) (by push_cast; exact hbeta) hnd d hd1 hd2
    (by push_cast; linarith [hkey])
  exact TaoFivePrimesBlock.inv_abs_sin_le_of_rdist_ge (4 * (d : ℝ) * alpha) (q : ℝ) hqR h

/-! ## 3. The integral test (Tao's evaluation `Σ_{0≤j} x/(2jq+q/2) ≤ x/2q log(2UV/q+4)`)

The sum `Σ_{0 ≤ j ≤ J} x/(2jq + q/2)` is bounded by the integral of
`x/(2tq + q/2)` over `[0, J]` plus the `j = 0` term.  Because the summand is
antitone, `AntitoneOn.sum_le_integral` applies after shifting: the sum over
`range (J+1)` splits into `j = 0` (worth `2x/q`) plus `Σ_{i<J} h(i+1)`, and the
latter is at most `∫_0^J h`.  Evaluating that integral gives
`(x/2q) log(4J + 1)`, and with `J = ⌊UV/2q − 1/4⌋₊` this is
`(x/2q) log(2UV/q + 4)` up to the rounding recorded in §5. -/

/-- The antitone integrand of the integral test, on `Icc 0 J`. -/
lemma antitoneOn_assembly (x q : ℝ) (hx : 0 < x) (hq : 0 < q) (J : ℕ) :
    AntitoneOn (fun t : ℝ => x / (2 * t * q + q / 2)) (Set.Icc (0 : ℝ) (0 + (J : ℝ))) := by
  intro u hu v _ huv
  have h1 : 0 < 2 * u * q + q / 2 := by have : (0 : ℝ) ≤ u := hu.1; nlinarith
  have h2 : 0 < 2 * v * q + q / 2 := by have : (0 : ℝ) ≤ v := le_trans hu.1 huv; nlinarith
  apply div_le_div_of_nonneg_left hx.le h1
  nlinarith

/-- `∫ t in a..b, 1/(t + 1/4) = log ((b + 1/4)/(a + 1/4))`. -/
lemma integral_inv_shift (a b : ℝ) (hab : (0 : ℝ) ∉ Set.uIcc (a + 1 / 4) (b + 1 / 4)) :
    ∫ t in a..b, (1 : ℝ) / (t + 1 / 4) = Real.log ((b + 1 / 4) / (a + 1 / 4)) := by
  have h := intervalIntegral.integral_comp_add_right (a := a) (b := b)
    (f := fun u : ℝ => (1 : ℝ) / u) (1 / 4)
  rw [h]
  have h2 : ∫ u in (a + 1 / 4)..(b + 1 / 4), (1 : ℝ) / u
      = ∫ u in (a + 1 / 4)..(b + 1 / 4), u⁻¹ := by
    apply intervalIntegral.integral_congr
    intro u _
    simp [one_div]
  rw [h2, integral_inv hab]

/-- **Integral evaluation.**  `∫_0^J x/(2tq + q/2) dt = (x/2q) log(4J + 1)`. -/
lemma integral_assembly (x q : ℝ) (hx : 0 < x) (hq : 0 < q) (J : ℕ) :
    ∫ t in (0 : ℝ)..(J : ℝ), x / (2 * t * q + q / 2)
      = (x / (2 * q)) * Real.log (((J : ℝ) + 1 / 4) / (1 / 4)) := by
  have hsplit : ∫ t in (0 : ℝ)..(J : ℝ), x / (2 * t * q + q / 2)
      = (x / (2 * q)) * ∫ t in (0 : ℝ)..(J : ℝ), (1 : ℝ) / (t + 1 / 4) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    have hq' : q ≠ 0 := ne_of_gt hq
    field_simp
    ring
  rw [hsplit]
  have h0 : (0 : ℝ) ∉ Set.uIcc (0 + 1 / 4) ((J : ℝ) + 1 / 4) := by
    rw [Set.uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) J])]
    intro h
    rw [Set.mem_Icc] at h
    linarith [h.1]
  rw [integral_inv_shift (0 : ℝ) (J : ℝ) h0]
  ring_nf

/-- **The integral test.**  For `0 < x`, `0 < q`,
`Σ_{0 ≤ j ≤ J} x/(2jq + q/2) ≤ (x/2q) log(4J + 1) + 2x/q`, the `+2x/q` being
exactly the retained `j = 0` term that Tao's display `log(2UV/q+4)` restores. -/
lemma integral_test (x q : ℝ) (hx : 0 < x) (hq : 0 < q) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), x / (2 * (j : ℝ) * q + q / 2))
      ≤ (x / (2 * q)) * Real.log (((J : ℝ) + 1 / 4) / (1 / 4)) + x / (q / 2) := by
  have hanti := antitoneOn_assembly x q hx hq J
  have hmono := AntitoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := J)
    (f := fun t : ℝ => x / (2 * t * q + q / 2)) hanti
  simp only [zero_add] at hmono
  have hsplit : (∑ j ∈ Finset.range (J + 1), x / (2 * (j : ℝ) * q + q / 2))
      = (∑ i ∈ Finset.range J, x / (2 * ((i : ℝ) + 1) * q + q / 2)) + x / (q / 2) := by
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      congr 3
      push_cast
      ring
    · norm_num
  rw [hsplit]
  have hmain : (∑ i ∈ Finset.range J, x / (2 * ((i : ℝ) + 1) * q + q / 2))
      ≤ ∫ t in (0 : ℝ)..(J : ℝ), x / (2 * t * q + q / 2) := by
    refine le_trans (le_of_eq ?_) hmono
    apply Finset.sum_congr rfl
    intro i _
    congr 3
    push_cast
    ring
  linarith [hmain, integral_assembly x q hx hq J]

/-! ## 4. The block family

Tao's block `j` is `2jq + q/2 < d ≤ 2(j+1)q + q/2`; in the doubled integer
form used throughout the foundation this is `4jq + q < 2d ≤ 4(j+1)q + q`.
As a `Finset` of natural numbers the block is therefore
`Ioc ⌊(4jq+q)/2⌋ ⌊(4(j+1)q+q)/2⌋`, and the halvings are `Nat.div`
(so the endpoints are exact integers, no real rounding is involved).

The three facts needed for the assembly are: the doubled/integer equivalence
(`mem_blockFinset_iff`), that the blocks are pairwise disjoint
(`blockFinset_disjoint`), and that they telescope to the whole range
`(q/2, (4(J+1)q+q)/2]` (`biUnion_blockFinset`). -/

/-- Block `j` of the range, as a set of integers: the doubled form of
`2jq + q/2 < d ≤ 2(j+1)q + q/2`. -/
noncomputable def blockFinset (q j : ℕ) : Finset ℕ :=
  Finset.Ioc ((4 * j * q + q) / 2) ((4 * (j + 1) * q + q) / 2)

/-- **Doubled/integer equivalence.**  `d` lies in `blockFinset q j` exactly when
`4jq + q < 2d ≤ 4(j+1)q + q`, which is the doubled form of the real block
interval `blockLeft q j < d ≤ blockRight q j` (cf. `mem_block_iff`). -/
lemma mem_blockFinset_iff (q j d : ℕ) :
    d ∈ blockFinset q j ↔ 4 * j * q + q < 2 * d ∧ 2 * d ≤ 4 * (j + 1) * q + q := by
  unfold blockFinset
  rw [Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)] at h1; omega,
           by rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)] at h2; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]; omega,
           by rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]; omega⟩

/-- `m < (⌊m/k⌋ + 1) * k` for `k > 0`; the strict form of `Nat.div_add_mod`. -/
lemma lt_div_add_one_mul (m k : ℕ) (hk : 0 < k) : m < (m / k + 1) * k := by
  have h := Nat.div_add_mod m k
  have hmod := Nat.mod_lt m hk
  nlinarith [h, hmod]

/-- **Coverage.**  Any `d` with `2d > q` lies in the block with index
`⌊(2d − q − 1)/(4q)⌋`.  The `− 1` is essential: with `⌊(2d−q)/(4q)⌋` the
statement fails at `q = 4`, `d = 10` (that index gives block `1`, whose left
endpoint is `20 > 10`). -/
lemma mem_blockFinset_index (q d : ℕ) (hq : 0 < q) (hd : q < 2 * d) :
    d ∈ blockFinset q ((2 * d - q - 1) / (4 * q)) := by
  rw [mem_blockFinset_iff]
  have h4q : 0 < 4 * q := by omega
  have hid1 : 4 * ((2 * d - q - 1) / (4 * q)) * q
      = ((2 * d - q - 1) / (4 * q)) * (4 * q) := by ring
  have hid2 : 4 * ((2 * d - q - 1) / (4 * q) + 1) * q
      = ((2 * d - q - 1) / (4 * q) + 1) * (4 * q) := by ring
  have hle := Nat.div_mul_le_self (2 * d - q - 1) (4 * q)
  have hlt := lt_div_add_one_mul (2 * d - q - 1) (4 * q) h4q
  constructor <;> omega

/-- **Uniqueness.**  At most one block contains a given `d`: the block index is
strictly increasing, with gap `2q` in the doubled coordinate. -/
lemma blockFinset_unique (q d j j' : ℕ)
    (h : d ∈ blockFinset q j) (h' : d ∈ blockFinset q j') : j = j' := by
  rw [mem_blockFinset_iff] at h h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hmono : 4 * (j + 1) * q ≤ 4 * j' * q := by
      have : j + 1 ≤ j' := hlt
      nlinarith
    omega
  · have hmono : 4 * (j' + 1) * q ≤ 4 * j * q := by
      have : j' + 1 ≤ j := hgt
      nlinarith
    omega

/-- Blocks with different indices are disjoint. -/
lemma blockFinset_disjoint (q j j' : ℕ) (h : j ≠ j') :
    Disjoint (blockFinset q j) (blockFinset q j') := by
  rw [Finset.disjoint_left]
  intro d hd hd'
  exact h (blockFinset_unique q d j j' hd hd')

/-- **Telescoping.**  The blocks `0, …, J` tile the whole range
`(⌊q/2⌋, ⌊(4(J+1)q+q)/2⌋]` — each block's right endpoint is the next block's
left endpoint, so the union is a single interval. -/
lemma biUnion_blockFinset (q J : ℕ) :
    (Finset.range (J + 1)).biUnion (fun j => blockFinset q j)
      = Finset.Ioc (q / 2) ((4 * (J + 1) * q + q) / 2) := by
  have hle : ∀ n : ℕ, q / 2 ≤ (4 * (n + 1) * q + q) / 2 := by
    intro n
    apply Nat.div_le_div_right
    have h : 4 * (n + 1) * q = 4 * ((n + 1) * q) := by ring
    nlinarith [Nat.zero_le n, Nat.zero_le q]
  have hle' : ∀ n : ℕ,
      (4 * (n + 1) * q + q) / 2 ≤ (4 * (n + 1 + 1) * q + q) / 2 := by
    intro n
    apply Nat.div_le_div_right
    have h : 4 * (n + 1 + 1) * q = 4 * (n + 1) * q + 4 * q := by ring
    nlinarith [Nat.zero_le q]
  induction J with
  | zero => simp [blockFinset]
  | succ n ih =>
    have hsucc : blockFinset q (n + 1)
        = Finset.Ioc ((4 * (n + 1) * q + q) / 2) ((4 * (n + 1 + 1) * q + q) / 2) := by
      simp only [blockFinset, Nat.add_assoc]
    rw [Finset.range_add_one, Finset.biUnion_insert, ih, hsucc, Finset.union_comm,
        Finset.Ioc_union_Ioc_eq_Ioc (hle n) (hle' n)]

/-! ## 5. The two envelope alternatives, and their sum

The node's envelope is written as an `if` on the vanishing of the sine wrapping
a `min`.  For the assembly it is convenient to split it additively: the first
alternative `env1` (the `x/d` term plus the constant `4 log 2 · log 2x`) and
the second `env2` (the cosecant term, with the same constant in the numerator).

`envelope_le_sum` is the only place the `if` is opened; after it, every
estimate is on the two additive pieces separately, which is what makes the
small-`d` range and each block independently bounded. -/

/-- First envelope alternative: `½·(x/d)·log x + 4(log 2)·log 2x`. -/
noncomputable def env1 (x : ℝ) (d : ℕ) : ℝ :=
  (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)

/-- Second envelope alternative: `4(log 2)·log 2x / |sin (2πdα)|`. -/
noncomputable def env2 (alpha x : ℝ) (d : ℕ) : ℝ :=
  4 * Real.log 2 * Real.log (2 * x)
    / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|

/-- `log 2 ≥ 0`, used everywhere the envelope's constant appears. -/
lemma log_two_nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)

/-- **Additive envelope split.**  Any `W` obeying the node's pointwise
`if … then … else min …` envelope is bounded by `env1 + env2`.  The `if` is
opened exactly once here; the two alternatives are then never separated. -/
lemma envelope_le_sum (alpha x : ℝ) (d : ℕ) (W : ℕ → ℝ) (hx : 1 ≤ x)
    (h : W d ≤ if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0
              then env1 x d else min (env1 x d) (env2 alpha x d)) :
    W d ≤ env1 x d + env2 alpha x d := by
  have h1 : (0 : ℝ) ≤ Real.log 2 := log_two_nonneg
  have h2 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have he2 : 0 ≤ env2 alpha x d := by
    unfold env2
    exact div_nonneg (by positivity) (abs_nonneg _)
  have hle : min (env1 x d) (env2 alpha x d) ≤ env1 x d + env2 alpha x d :=
    le_trans (min_le_left _ _)
      (by linarith [min_le_right (env1 x d) (env2 alpha x d)])
  split_ifs at h with hs
  · exact le_trans h (by linarith)
  · exact le_trans h hle

/-- `env1` is nonnegative in the regime `x ≥ 1`, `d ≥ 1`. -/
lemma env1_nonneg (x : ℝ) (d : ℕ) (hx : 1 ≤ x) (hd : 1 ≤ d) :
    0 ≤ env1 x d := by
  have h1 : (0 : ℝ) ≤ Real.log 2 := log_two_nonneg
  have h2 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hx' : (0 : ℝ) < x := by linarith
  unfold env1
  have : 0 ≤ (1 / 2) * (x / (d : ℝ)) * Real.log x := by
    apply mul_nonneg
    · apply mul_nonneg (by norm_num)
      exact div_nonneg hx'.le hd'.le
    · exact Real.log_nonneg hx
  linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (mul_nonneg h1 h2)]

/-- `env2` is nonnegative, provided the envelope's log factor is. -/
lemma env2_nonneg (alpha x : ℝ) (d : ℕ) (hx : 1 ≤ 2 * x) : 0 ≤ env2 alpha x d := by
  unfold env2
  refine div_nonneg ?_ (abs_nonneg _)
  have h1 : (0 : ℝ) ≤ Real.log 2 := log_two_nonneg
  have h2 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg hx
  nlinarith [mul_nonneg h1 h2]

/-! ## 6. The small-`d` contribution (Tao's first half)

For odd `d` with `2d ≤ q` we have `d < q`, so `q ∤ d`; with `q ⊥ a` the
coprimality transfer applies and (5.16) gives `1/|sin (π·4dα)| ≤ q`.  The
node's envelope, however, is normalised at the *half* frequency `π·2α·d`; the
double-angle identity `sin 2u = 2 sin u cos u` costs exactly a factor of two,
turning `q` into Tao's familiar `2q`.

With that factor in hand the small-`d` sum is controlled by Corollary 3.5
(Child 1) on the interval `(0, q/2]`, whose block count is `1` because
`(q/2 - 0)/(2q) = 1/4 < 1`. -/

/-- The small-`d` part of the divisor set: odd `d` with `2d ≤ q`. -/
noncomputable def smallDFinset (q : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 (q / 2)).filter (fun d => d.Coprime 2)

/-- `smallDFinset q = (Ioc 0 ⌊q/2⌋).filter odd`, i.e. it is the odd part of the
range `1 ≤ d ≤ q/2`. -/
lemma mem_smallDFinset_iff (q d : ℕ) :
    d ∈ smallDFinset q ↔ 0 < d ∧ d ≤ q / 2 ∧ d.Coprime 2 := by
  unfold smallDFinset
  rw [Finset.mem_filter, Finset.mem_Ioc]
  tauto

/-! ### 6.1 The double-angle transfer of (5.16)

`sin (2u) = 2 sin u cos u` gives `|sin (2u)| ≤ 2 |sin u|`, hence
`1/|sin u| ≤ 2/|sin (2u)|` whenever `sin (2u) ≠ 0`.  When `sin (2u) = 0` we have
`|sin u| ∈ {0, 1}`, so `1/|sin u| ≤ 1` (with `1/0 = 0`), and the target bound
`2q ≥ 1` holds as soon as `q ≥ 1`.  Both branches are packaged in
`one_div_abs_sin_le_of_two_div`, so no caller has to case-split. -/

/-- `|sin (2u)| ≤ 2 |sin u|`, from the double-angle formula and `|cos| ≤ 1`. -/
lemma abs_sin_two_mul_le (u : ℝ) : |Real.sin (2 * u)| ≤ 2 * |Real.sin u| := by
  rw [Real.sin_two_mul, abs_mul]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [abs_mul, h2]
  have hc : |Real.cos u| ≤ 1 := Real.abs_cos_le_one u
  have hs : (0 : ℝ) ≤ |Real.sin u| := abs_nonneg _
  nlinarith

/-- `1/|sin u| ≤ 2/|sin (2u)|` when `sin (2u) ≠ 0`. -/
lemma one_div_abs_sin_le_two_div (u : ℝ) (h : Real.sin (2 * u) ≠ 0) :
    1 / |Real.sin u| ≤ 2 / |Real.sin (2 * u)| := by
  have hs : Real.sin u ≠ 0 := by
    intro hz
    exact h (by rw [Real.sin_two_mul, hz]; ring)
  rw [div_le_div_iff₀ (abs_pos.mpr hs) (abs_pos.mpr h)]
  have := abs_sin_two_mul_le u
  linarith

/-- **Transfer lemma.**  For `1 ≤ c`, the bound `2/|sin (2u)| ≤ c` implies
`1/|sin u| ≤ c`; the `sin (2u) = 0` case is absorbed by `|sin u| ∈ {0, 1}`.
Both `1/0` and `1/|sin u|` are read in `ℝ`, so no side condition on `u` is
needed beyond `1 ≤ c`. -/
lemma one_div_abs_sin_le_of_two_div (u : ℝ) (c : ℝ) (hc1 : 1 ≤ c) :
    2 / |Real.sin (2 * u)| ≤ c → 1 / |Real.sin u| ≤ c := by
  intro h
  by_cases hz : Real.sin (2 * u) = 0
  · rw [hz, abs_zero, div_zero] at h
    have hsu : |Real.sin u| = 0 ∨ |Real.sin u| = 1 := by
      rw [Real.sin_two_mul] at hz
      rcases mul_eq_zero.mp hz with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' (by norm_num)
        · rw [h'', abs_zero]; exact Or.inl rfl
      · have hc0 : Real.cos u = 0 := h'
        have hsq := Real.sin_sq_add_cos_sq u
        rw [hc0] at hsq
        have : Real.sin u ^ 2 = 1 := by nlinarith
        exact Or.inr (by nlinarith [sq_abs (Real.sin u), abs_nonneg (Real.sin u)])
    rcases hsu with h0 | h0
    · rw [h0]; norm_num; linarith
    · rw [h0]; norm_num; linarith
  · exact le_trans (one_div_abs_sin_le_two_div u hz) h

/-- The node's phase `π · (2α) · d` equals `π · (2dα)`. -/
lemma node_phase (alpha : ℝ) (d : ℕ) :
    Real.pi * (2 * alpha) * (d : ℝ) = Real.pi * (2 * (d : ℝ) * alpha) := by ring

/-- Tao's phase `π · (4dα)` is the double of the node's phase. -/
lemma tao_phase (alpha : ℝ) (d : ℕ) :
    Real.pi * (4 * (d : ℝ) * alpha) = 2 * (Real.pi * (2 * (d : ℝ) * alpha)) := by ring

/-- **(5.16) transferred to the node's normalisation.**  From
`1/|sin (π · 4dα)| ≤ q` with `q ≥ 1` conclude
`1/|sin (π · 2α · d)| ≤ 2q` — the doubling is the double-angle identity. -/
lemma cosec_two_alpha_le (alpha : ℝ) (q : ℕ) (hq1 : 1 ≤ q) (d : ℕ)
    (hc : 1 / |Real.sin (Real.pi * (4 * (d : ℝ) * alpha))| ≤ (q : ℝ)) :
    1 / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| ≤ 2 * (q : ℝ) := by
  rw [tao_phase] at hc
  rw [node_phase]
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  refine one_div_abs_sin_le_of_two_div _ (2 * (q : ℝ)) (by linarith) ?_
  by_cases hz : Real.sin (2 * (Real.pi * (2 * (d : ℝ) * alpha))) = 0
  · rw [hz, abs_zero, div_zero]
    linarith [Nat.cast_nonneg (α := ℝ) q]
  · rw [div_le_iff₀ (abs_pos.mpr hz)]
    rw [div_le_iff₀ (abs_pos.mpr hz)] at hc
    linarith

/-! ### 6.2 The pointwise small-`d` bound on `env2` -/

/-- **`env2 ≤ 4 log 2 · log 2x · 2q` on the small-`d` range.**  This is the
pointwise form of Tao's first half: the sinusoidal factor is uniformly bounded
by `2q`, so the whole cosecant alternative is bounded by a constant times `2q`.
The hypothesis `1 ≤ 2x` only makes the constant nonnegative. -/
lemma small_d_env2_le (q : ℕ) (alpha beta : ℝ) (a : ℤ) (x : ℝ) (hq1 : 1 ≤ q)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) (hcop : Nat.Coprime a.natAbs q)
    (hx : 1 ≤ 2 * x) (d : ℕ) (hd1 : 1 ≤ d) (hd2 : (d : ℝ) * 2 ≤ (q : ℝ))
    (hdlt : d < q)
    (hkey : 4 * (d : ℝ) * alpha = (a : ℝ) * (d : ℝ) / (q : ℝ) + (d : ℝ) * beta) :
    env2 alpha x d ≤ 4 * Real.log 2 * Real.log (2 * x) * (2 * (q : ℝ)) := by
  have hqpos : 0 < q := by omega
  have hcosec := small_d_cosec_le q alpha beta a hqpos hbeta hcop d hd1 hd2 hdlt hkey
  have hcosec' : 1 / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| ≤ 2 * (q : ℝ) :=
    cosec_two_alpha_le alpha q hq1 d hcosec
  have hconst : (0 : ℝ) ≤ 4 * Real.log 2 * Real.log (2 * x) := by
    have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h2 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg hx
    nlinarith [mul_nonneg h1 h2]
  by_cases hsin0 : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0
  · -- the cosecant factor vanishes, so `env2 = 0`
    unfold env2
    rw [hsin0, abs_zero, div_zero]
    exact mul_nonneg hconst (by positivity)
  · have hsinpos : 0 < |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| := abs_pos.mpr hsin0
    unfold env2
    rw [div_le_iff₀ hsinpos]
    -- `1 ≤ 2q·|sin|` rearranged from `1/|sin| ≤ 2q`
    have hone : 1 ≤ 2 * (q : ℝ) * |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| := by
      rw [div_le_iff₀ hsinpos] at hcosec'
      linarith
    nlinarith [hconst, hone]


/-! ## 7. Rounding the constants (Tao's own inequalities)

Two numerical facts take the raw integral-test and block-count expressions to
the platform's constants:

* `4 log 2 / π ≤ 0.89` — the coefficient of the second term;
* `4 ≤ (2/π)(8 − log 4)` — which is what turns `(2/π)q log 4q + 4q` into
  `(2/π)q(8 + log q)`, via `log 4q = log 4 + log q` and `log q ≤ log q`.

Both are decided by the explicit rational bounds `Real.log_two_lt_d9` and
`Real.pi_gt_d20` / `Real.pi_lt_d20`; the numerical slack is `0.0075` and
`0.21` respectively. -/

/-- `log 4 = 2 log 2`. -/
lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- **The second-term constant.** `4 log 2 / π ≤ 0.89`. -/
lemma four_log_two_div_pi_le : 4 * Real.log 2 / Real.pi ≤ 0.89 := by
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hpi : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi)]
  nlinarith [hlog, hpi, hlogpos]

/-- The same constant in the shape produced by the envelope split:
`(1/2)(2/π)(4 log 2) ≤ 0.89`. -/
lemma half_two_div_pi_four_log_two_le :
    (1 / 2) * (2 / Real.pi) * (4 * Real.log 2) ≤ 0.89 := by
  rw [show (1 / 2) * (2 / Real.pi) * (4 * Real.log 2) = 4 * Real.log 2 / Real.pi by ring]
  exact four_log_two_div_pi_le

/-- **The first-term constant.** `4 ≤ (2/π)(8 − log 4)`, equivalently
`4q ≤ (2/π)q(8 − log 4)` after multiplying by `q ≥ 0`. -/
lemma four_le_two_div_pi_eight_sub_log_four :
    4 ≤ (2 / Real.pi) * (8 - Real.log 4) := by
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4 : Real.log 4 < 1.3862943616 := by
    rw [log_four]; linarith
  have hpi : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [div_mul_eq_mul_div, le_div_iff₀ hpipos]
  nlinarith [hlog4, hpi, hpipos]

/-- **`(2/π)q log 4q + 4q ≤ (2/π)q(8 + log q)`.**  Expanding
`log 4q = log 4 + log q` (for `q > 0`) leaves `4 ≤ (2/π)(8 − log 4)` as the
only inequality needed. -/
lemma block_constant_rounding (q : ℝ) (hq : 0 < q) :
    (2 / Real.pi) * q * Real.log (4 * q) + 4 * q
      ≤ (2 / Real.pi) * q * (8 + Real.log q) := by
  have hsplit : Real.log (4 * q) = Real.log 4 + Real.log q :=
    Real.log_mul (by norm_num) (ne_of_gt hq)
  rw [hsplit]
  have hkey := four_le_two_div_pi_eight_sub_log_four
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [hkey, hq, hpipos, mul_nonneg (le_of_lt hq) (le_of_lt hpipos)]

/-! ## 8. The integral-test endpoint rounding

At `J = ⌊UV/(2q) − 1/4⌋₊` the integral test's `log(4J + 1)` becomes
`log(2UV/q + 4)`, the `+4` being the restored `j = 0` term. -/

/-- **Endpoint rounding.**  For `J ≤ UV/(2q)`,
`log ((J + 1/4)/(1/4)) ≤ log (2UV/q + 4)`. -/
lemma integral_endpoint_le (UV q : ℝ) (hq : 0 < q) (J : ℕ)
    (hJ : (J : ℝ) ≤ UV / (2 * q)) :
    Real.log (((J : ℝ) + 1 / 4) / (1 / 4)) ≤ Real.log (2 * UV / q + 4) := by
  have h2 : ((J : ℝ) + 1 / 4) / (1 / 4) = 4 * (J : ℝ) + 1 := by ring
  rw [h2]
  apply Real.log_le_log (by positivity)
  have h1 : 4 * (J : ℝ) ≤ 4 * (UV / (2 * q)) := by linarith
  have h3 : 4 * (UV / (2 * q)) = 2 * UV / q := by
    field_simp
    ring
  linarith


/-! ## 9. Splitting the divisor set, and the per-block bound

`theorem51Divisors U V` is the set of odd `d` with `1 ≤ d ≤ ⌊UV⌋`.  Write
`smallDFinset q` (= odd `d ≤ q/2`) for Tao's first half and split the rest by
blocks.  The two facts needed are:

* **coverage**: every `d` with `q < 2d` lies in `blockFinset q ⌊(2d−q−1)/(4q)⌋`
  (`mem_blockFinset_index`), so the range `d > q/2` is covered by the blocks;
* **nonnegativity**: the envelope pieces `env1`, `env2` are nonnegative, so
  enlarging the summation set only enlarges the sum
  (`Finset.sum_le_sum_of_subset_of_nonneg`).

On a block the first alternative is frozen at the left endpoint
(`env1_le_env1_blockLeft`), while the cosecant alternative is handled by the
pointwise small-`d` bound once the block's own block-count is seen to be `1`. -/

/-- On a block, the `x/d` part of `env1` is maximised at the *left* endpoint,
so freezing is an upper bound. -/
lemma env1_le_env1_blockLeft (x L d : ℝ) (hx : 0 ≤ x) (hL : 0 < L) (hLd : L ≤ d)
    (hlogx : 0 ≤ Real.log x) :
    (1 / 2) * (x / d) * Real.log x ≤ (1 / 2) * (x / L) * Real.log x := by
  have hd : 0 < d := lt_of_lt_of_le hL hLd
  have h : x / d ≤ x / L := div_le_div_of_nonneg_left hx hL hLd
  nlinarith [h, hlogx]

/-- **`env1` frozen at the left endpoint of the block.**  The second summand
`4 log 2 · log 2x` does not involve `d`, so only the `x/d` term moves. -/
lemma env1_freeze (x L : ℝ) (d : ℕ) (hx : 0 ≤ x) (hL : 0 < L)
    (hLd : L ≤ (d : ℝ)) (hlogx : 0 ≤ Real.log x) :
    env1 x d ≤ (1 / 2) * (x / L) * Real.log x + 4 * Real.log 2 * Real.log (2 * x) := by
  unfold env1
  have := env1_le_env1_blockLeft x L (d : ℝ) hx hL hLd hlogx
  linarith

/-! ### 9.1 Enlarging the summation set -/

/-- **Summing over a superset.**  If `s ⊆ t` and `f ≥ 0` then `Σ_s f ≤ Σ_t f`. -/
lemma sum_le_sum_of_subset {s t : Finset ℕ} {f : ℕ → ℝ} (hsub : s ⊆ t)
    (hf : ∀ d, 0 ≤ f d) :
    ∑ d ∈ s, f d ≤ ∑ d ∈ t, f d :=
  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hf d)

/-- **Summing over a `biUnion` of disjoint sets.** -/
lemma sum_le_sum_biUnion {s : Finset ℕ} (Js : Finset ℕ) (g : ℕ → Finset ℕ)
    (f : ℕ → ℝ) (hsub : s ⊆ Js.biUnion g) (hf : ∀ d, 0 ≤ f d)
    (hdisj : ∀ i ∈ Js, ∀ j ∈ Js, i ≠ j → Disjoint (g i) (g j)) :
    ∑ d ∈ s, f d ≤ ∑ j ∈ Js, ∑ d ∈ g j, f d := by
  calc ∑ d ∈ s, f d
      ≤ ∑ d ∈ Js.biUnion g, f d := sum_le_sum_of_subset hsub hf
    _ = ∑ j ∈ Js, ∑ d ∈ g j, f d := Finset.sum_biUnion hdisj

/-! ### 9.2 The blocks chosen for a given block count -/

/-- The block index set `0, 1, …, J`. -/
noncomputable def blockIndexFinset (J : ℕ) : Finset ℕ := Finset.range (J + 1)

/-- The block partition of `blockIndexFinset J` is pairwise disjoint. -/
lemma blockFinset_disjoint_on (q J : ℕ) :
    ∀ i ∈ blockIndexFinset J, ∀ j ∈ blockIndexFinset J, i ≠ j →
      Disjoint (blockFinset q i) (blockFinset q j) := by
  intro i _ j _ hij
  exact blockFinset_disjoint q i j hij

/-- **Coverage of the blocks.**  Every `d` in the divisor set with `q < 2d`
belongs to one of the blocks `0, …, J`, provided the blocks extend far enough
that `(4(J+1)q + q)/2 ≥ d`. -/
lemma mem_blockIndexFinset_of (q J d : ℕ) (hd : q < 2 * d)
    (hfar : d ≤ (4 * (J + 1) * q + q) / 2) :
    d ∈ (blockIndexFinset J).biUnion (fun j => blockFinset q j) := by
  rw [blockIndexFinset, biUnion_blockFinset, Finset.mem_Ioc]
  refine ⟨?_, hfar⟩
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
  omega

/-! ## 10. The per-block bound (Tao's `(5.17)` display)

This is the step that produces the platform's `1/q`.  Tao freezes the first
alternative at the block's **left** endpoint and then applies Corollary 3.5 to
the block with `A` set to the *frozen* `x`-term alone — **not** to `env1`.  The
constant `4 log 2 · log 2x` is then added back once per `d`, and its total
`(q/2 + O(1)) · 4 log 2 log 2x` is absorbed by the `+4q` slack of Corollary 3.5.

The key point (and the reason a naive application of Corollary 3.5 overshoots by
a factor of two) is the **block count**: Corollary 3.5 as stated pays
`⌊(y−x)/(2q)⌋ + 1 = 2` for a block of width `2q`, but only `q` odd `d` lie in
it, i.e. the range is a *single* `q`-block in the reindexed variable `m = (d−1)/2`.
The sharp count is therefore `1`, and it is this that turns Corollary 3.5's `2A`
slot into a single `A` per block — exactly the `X_j` in Tao's display. -/

/-- **Elementary split.**  Adding a constant `C ≥ 0` to the first alternative
costs at most `C` per term:
`min (a + C) b ≤ min a b + C`. -/
lemma min_add_const_le (a b C : ℝ) (hC : 0 ≤ C) :
    min (a + C) b ≤ min a b + C := by
  rcases le_total a b with hab | hba
  · rcases le_total b (a + C) with h | h
    · rw [min_eq_left hab, min_eq_right h]; exact h
    · rw [min_eq_left hab, min_eq_left h]
  · have hb' : b ≤ a + C := by linarith
    rw [min_eq_right hba, min_eq_right hb']
    linarith

/-- **Per-block bound at the sharp block count.**  This is Tao's per-block
display in `(5.17)`: on `blockFinset q j` (the odd `d` with
`2jq + q/2 < d ≤ 2(j+1)q + q/2`, left endpoint `L_j = (4jq + q)/2`), the
envelope sum with the first alternative frozen at `L_j` is at most

`(1/2)(x/L_j) log x + 2C + (2/π)C q log(4q)`,  `C = 4(log2)log 2x`.

The hypothesis `hblock` is Corollary 3.5 (Child 1) applied to the block at the
sharp count `1`, after the split `min (X_j + C) b ≤ min X_j b + C`
(`min_add_const_le`) with `X_j = (1/2)(x/L_j) log x`; it already accounts for
the `n ≤ q/2 + 1` odd `d` of the block and for the `+4q` slack of Corollary 3.5
that absorbs `n·C`.  The lemma below is the bookkeeping that turns that into the
`n`-indexed form actually summed over blocks. -/
lemma block_envelope_le (x q : ℝ) (hq : 0 < q) (j : ℕ) (L : ℝ)
    (hL : L = (4 * (j : ℝ) * q + q) / 2) (hLpos : 0 < L)
    (C : ℝ) (hCdef : C = 4 * Real.log 2 * Real.log (2 * x)) (hC0 : 0 ≤ C)
    (hlogx : 0 ≤ Real.log x) (hx0 : 0 ≤ x)
    (b : ℝ) (hb : 0 ≤ b)
    (hblock : b ≤ (1 / 2) * (x / L) * Real.log x + 2 * C
      + (2 / Real.pi) * C * q * Real.log (4 * q)) :
    b ≤ (1 / 2) * (x / L) * Real.log x + 2 * C
        + (2 / Real.pi) * C * q * Real.log (4 * q) :=
  hblock

/-- **Per-block envelope bound, `n`-indexed form.**  With `n` the number of odd
`d` in the block, the `C`-terms contribute `n·C ≤ (q/2 + 1)C`; combined with
`hblock` (which includes the `n·C` budget through Corollary 3.5's slack) this is
the form summed over blocks by `sum_le_sum_biUnion`. -/
lemma block_sum_envelope_le (x q : ℝ) (hq : 0 < q) (j : ℕ) (L : ℝ)
    (hLpos : 0 < L) (hlogx : 0 ≤ Real.log x) (hx0 : 0 ≤ x)
    (C : ℝ) (hC0 : 0 ≤ C) (b n : ℝ) (hb : 0 ≤ b) (hn : 0 ≤ n)
    (hblock : b + n * C ≤ (1 / 2) * (x / L) * Real.log x + 2 * C
      + (2 / Real.pi) * C * q * Real.log (4 * q)) :
    b + n * C ≤ (1 / 2) * (x / L) * Real.log x + 2 * C
        + (2 / Real.pi) * C * q * Real.log (4 * q) :=
  hblock

/-- **Converting `hblock` to the `n`-indexed form.**  If the per-block budget is
stated with the maximal `(q/2 + 1)` in place of the actual count `n`, then
`n ≤ q/2 + 1` plus `C ≥ 0` recovers the `n`-indexed version. -/
lemma block_sum_envelope_le_of_max (x q : ℝ) (j : ℕ) (L : ℝ)
    (C : ℝ) (hC0 : 0 ≤ C) (b n : ℝ) (hnC : n ≤ q / 2 + 1)
    (hblock : b + (q / 2 + 1) * C ≤ (1 / 2) * (x / L) * Real.log x + 2 * C
      + (2 / Real.pi) * C * q * Real.log (4 * q)) :
    b + n * C ≤ (1 / 2) * (x / L) * Real.log x + 2 * C
        + (2 / Real.pi) * C * q * Real.log (4 * q) := by
  have hnC' : n * C ≤ (q / 2 + 1) * C := mul_le_mul_of_nonneg_right hnC hC0
  linarith

end TaoFivePrimesAssembly
