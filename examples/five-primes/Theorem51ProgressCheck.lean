import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.FiniteSupport.Basic
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Definitions.Def_TaoFivePrimes_Theorem51Scale
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- Source: examples/five-primes/Theorem51VaughanIdentity.lean
section

open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TaoFivePrimes

/-- Real cutoffs retain the exact parameter domain of Theorem 5.1. -/
noncomputable def vaughanBelow (f : ArithmeticFunction ℝ) (X : ℝ) :
    ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ X then f n else 0, by split_ifs <;> simp⟩

noncomputable def vaughanAbove (f : ArithmeticFunction ℝ) (X : ℝ) :
    ArithmeticFunction ℝ := f - vaughanBelow f X

noncomputable def vaughanHalfLog : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log n / 2, by simp⟩

noncomputable def vaughanCentered (V : ℝ) : ArithmeticFunction ℝ :=
  vaughanAbove Λ V * ζ - vaughanHalfLog

/-- The exact centered convolution identity, before restricting to the cutoff
support and moving the half-log correction to the Type I sum. -/
theorem vaughan_centered_identity (U V : ℝ) :
    (Λ : ArithmeticFunction ℝ) =
      vaughanBelow Λ V + vaughanBelow μ U * ArithmeticFunction.log -
        vaughanBelow μ U * vaughanBelow Λ V * ζ +
        vaughanAbove μ U * vaughanCentered V +
        vaughanAbove μ U * vaughanHalfLog := by
  unfold vaughanCentered vaughanAbove
  rw [← ArithmeticFunction.vonMangoldt_mul_zeta]
  have hz : (μ : ArithmeticFunction ℝ) * ζ = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  calc
    _ = μ * Λ * ζ + vaughanBelow Λ V * (1 - μ * ζ) := by
      rw [mul_right_comm, hz]
      simp
    _ = _ := by ring

/-- Evaluation of the high-cutoff function is a strict cutoff. -/
theorem vaughanAbove_apply (f : ArithmeticFunction ℝ) (X : ℝ) (n : ℕ) :
    vaughanAbove f X n = if X < (n : ℝ) then f n else 0 := by
  change f n - (if (n : ℝ) ≤ X then f n else 0) = _
  by_cases h : (n : ℝ) ≤ X
  · rw [if_pos h, if_neg (not_lt.mpr h), sub_self]
  · rw [if_neg h, if_pos (lt_of_not_ge h), sub_zero]

/-- The centered convolution coefficient equals the divisor-sum coefficient. -/
theorem vaughanCentered_apply (V : ℝ) (w : ℕ) :
    vaughanCentered V w =
      (∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)), Λ b) - Real.log w / 2 := by
  change (vaughanAbove Λ V * ζ) w - Real.log w / 2 = _
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp only [vaughanAbove_apply, Finset.sum_filter]

/-- The centered identity tested against a finitely supported complex weight.
The low von Mangoldt term vanishes when the weight vanishes below V. -/
theorem weighted_vaughan_centered_split (U V : ℝ) (s : Finset ℕ) (F : ℕ → ℂ)
    (hF : ∀ n ∈ s, (n : ℝ) ≤ V → F n = 0) :
    (∑ n ∈ s, (Λ n : ℂ) * F n) =
      (∑ n ∈ s,
        (((vaughanBelow μ U * ArithmeticFunction.log -
          vaughanBelow μ U * vaughanBelow Λ V * ζ +
          vaughanAbove μ U * vaughanHalfLog) n : ℝ) : ℂ) * F n) +
      (∑ n ∈ s, (((vaughanAbove μ U * vaughanCentered V) n : ℝ) : ℂ) * F n) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hid := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan_centered_identity U V)
  change Λ n = vaughanBelow Λ V n + (vaughanBelow μ U * ArithmeticFunction.log) n -
      (vaughanBelow μ U * vaughanBelow Λ V * ζ) n +
      (vaughanAbove μ U * vaughanCentered V) n +
      (vaughanAbove μ U * vaughanHalfLog) n at hid
  have hlow : (vaughanBelow Λ V n : ℂ) * F n = 0 := by
    change ((if (n : ℝ) ≤ V then Λ n else 0 : ℝ) : ℂ) * F n = 0
    by_cases h : (n : ℝ) ≤ V
    · rw [if_pos h, hF n hn h, mul_zero]
    · simp [h]
  change (Λ n : ℂ) * F n =
      (((vaughanBelow μ U * ArithmeticFunction.log) n -
        (vaughanBelow μ U * vaughanBelow Λ V * ζ) n +
        (vaughanAbove μ U * vaughanHalfLog) n : ℝ) : ℂ) * F n + _
  rw [hid]
  push_cast
  linear_combination hlow

/-- The high von Mangoldt convolution vanishes below its cutoff. -/
lemma vaughan_high_convolution_zero (V : ℝ) (w : ℕ) (hw : (w : ℝ) ≤ V) :
    (vaughanAbove Λ V * ζ) w = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro b hb
  rw [vaughanAbove_apply, if_neg]
  have hbw : b ≤ w := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hb).2)
    (Nat.mem_divisors.mp hb).1
  exact not_lt.mpr ((by exact_mod_cast hbw : (b : ℝ) ≤ w).trans hw)

/-- Restricting both centered terms restores the w > V support required by
Tao's actual Type II sum. -/
lemma vaughan_restricted_center_split (V : ℝ) :
    vaughanAbove Λ V * ζ =
      vaughanAbove (vaughanCentered V) V + vaughanAbove vaughanHalfLog V := by
  ext w
  change (vaughanAbove Λ V * ζ) w =
    vaughanAbove (vaughanCentered V) V w + vaughanAbove vaughanHalfLog V w
  rw [vaughanAbove_apply, vaughanAbove_apply]
  by_cases hw : V < (w : ℝ)
  · rw [if_pos hw, if_pos hw]
    change (vaughanAbove Λ V * ζ) w =
      (vaughanAbove Λ V * ζ) w - vaughanHalfLog w + vaughanHalfLog w
    ring
  · rw [if_neg hw, if_neg hw, add_zero]
    exact vaughan_high_convolution_zero V w (le_of_not_gt hw)

/-- Centered Vaughan identity with the correct w > V restriction. -/
theorem vaughan_restricted_centered_identity (U V : ℝ) :
    (Λ : ArithmeticFunction ℝ) =
      vaughanBelow Λ V + vaughanBelow μ U * ArithmeticFunction.log -
        vaughanBelow μ U * vaughanBelow Λ V * ζ +
        vaughanAbove μ U * vaughanAbove (vaughanCentered V) V +
        vaughanAbove μ U * vaughanAbove vaughanHalfLog V := by
  have hs : vaughanCentered V + vaughanHalfLog = vaughanAbove Λ V * ζ := by
    unfold vaughanCentered
    abel
  calc
    _ = vaughanBelow Λ V + vaughanBelow μ U * ArithmeticFunction.log -
        vaughanBelow μ U * vaughanBelow Λ V * ζ +
        vaughanAbove μ U * (vaughanCentered V + vaughanHalfLog) := by
      conv_lhs => rw [vaughan_centered_identity U V]
      ring
    _ = _ := by rw [hs, vaughan_restricted_center_split]; ring

/-- The half-log correction belongs to the d <= UV part on the required
support dw <= x <= UV^2. -/
lemma vaughan_half_log_correction_support (d w U V : ℝ)
    (hd : 0 < d) (hV : 0 < V) (hw : V < w)
    (hdw : d * w ≤ U * V ^ 2) : d ≤ U * V := by
  have hprod : d * V < U * V ^ 2 := (mul_lt_mul_of_pos_left hw hd).trans_le hdw
  have he : U * V ^ 2 = (U * V) * V := by ring
  rw [he] at hprod
  exact (lt_of_mul_lt_mul_right hprod hV.le).le

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51PhaseAudit.lean
section

namespace TaoFivePrimes

/-- Exact phase bounds for the positive unit numerator. -/
lemma unit_phase_window (alpha beta q : ℝ) (hq : 0 < q)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    (q - 1) / (4 * q ^ 2) ≤ alpha ∧ alpha ≤ (q + 1) / (4 * q ^ 2) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbeta
  have helo : (q - 1) / (4 * q ^ 2) = (1 / q - 1 / q ^ 2) / 4 := by
    field_simp
    <;> ring
  have hehi : (q + 1) / (4 * q ^ 2) = (1 / q + 1 / q ^ 2) / 4 := by
    field_simp
    <;> ring
  rw [helo, hehi]
  constructor <;> linarith

/-- The reversed sine comparison in the paragraph preceding (5.18)
cannot be used verbatim, even with beta = 0 and q = 1602. This is a
counterexample to that intermediate comparison, not to Theorem 5.1. -/
lemma source_typeI_sine_comparison_fails :
    ¬ (Real.sin (2 * Real.pi * (1 : ℝ) * (1 / (4 * 1602))) ≥
      Real.sin (2 * Real.pi * (1 : ℝ) / (4 * (1602 - 1)))) := by
  have hs : Real.sin (Real.pi / 3204) < Real.sin (Real.pi / 3202) := by
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith [Real.pi_pos]
  have he1 : 2 * Real.pi * (1 : ℝ) * (1 / (4 * 1602)) = Real.pi / 3204 := by ring
  have he2 : 2 * Real.pi * (1 : ℝ) / (4 * (1602 - 1)) = Real.pi / 3202 := by ring
  rw [he1, he2]
  exact not_le_of_gt hs

/-- The numerical parameters in the preceding comparison are in the
actual unit-numerator parameter regime. -/
lemma source_typeI_counterexample_parameters :
    (40 : ℝ) * 40 ≤ 6400 / 4 ∧
    (6400 : ℝ) ≤ 40 * 40 ^ 2 ∧
    (40 : ℝ) * 40 < 1602 - 1 ∧
    (40 : ℝ) < 6400 ∧
    4 * (1 / (4 * 1602) : ℝ) = 1 / 1602 + 0 ∧
    |(0 : ℝ)| ≤ 1 / (1602 : ℝ) ^ 2 := by norm_num

/-- A valid lower sine envelope, keeping the exact lower endpoint of the
phase window instead of substituting its upper endpoint. -/
lemma unit_phase_sine_lower (alpha beta q d : ℝ) (hq : 1 < q)
    (hd : 0 ≤ d) (hdq : d ≤ q - 1)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    Real.sin (2 * Real.pi * d * ((q - 1) / (4 * q ^ 2))) ≤
      Real.sin (2 * Real.pi * d * alpha) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hlo, hhi⟩ := unit_phase_window alpha beta q hq0 hphase hbeta
  have hqm : 0 < q - 1 := by linarith
  have ha : 0 ≤ alpha := le_trans (by positivity) hlo
  have hupper : alpha ≤ 1 / (4 * (q - 1)) := by
    apply hhi.trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hdalpha : d * alpha ≤ 1 / 4 := by
    calc
      _ ≤ (q - 1) * alpha := mul_le_mul_of_nonneg_right hdq ha
      _ ≤ (q - 1) * (1 / (4 * (q - 1))) :=
        mul_le_mul_of_nonneg_left hupper hqm.le
      _ = 1 / 4 := by field_simp
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · have hnonneg : 0 ≤ 2 * Real.pi * d * ((q - 1) / (4 * q ^ 2)) := by positivity
    linarith [Real.pi_pos]
  · have hm := mul_le_mul_of_nonneg_left hdalpha (show 0 ≤ 2 * Real.pi by positivity)
    nlinarith
  · exact mul_le_mul_of_nonneg_left hlo (by positivity)

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51TypeIIAlgebra.lean
section

namespace TaoFivePrimes

/-- A coupled radical estimate. The last two terms cannot be obtained by
termwise subadditivity alone; the hypothesis supplies the missing cross term. -/
lemma sqrt_four_terms_coupled (A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hCD : C ≤ 8 * D) :
    Real.sqrt (A + B + C + D) ≤
      Real.sqrt A + Real.sqrt B + Real.sqrt (C / 2) + Real.sqrt D := by
  have hsmall : Real.sqrt (C / 2) ≤ 2 * Real.sqrt D := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [Real.sq_sqrt hD]
  have hcross := mul_nonneg (Real.sqrt_nonneg (C / 2)) (sub_nonneg.mpr hsmall)
  have hrest := mul_nonneg
    (show 0 ≤ Real.sqrt A + Real.sqrt B by positivity)
    (show 0 ≤ Real.sqrt (C / 2) + Real.sqrt D by positivity)
  apply (Real.sqrt_le_left (by positivity)).2
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
    Real.sq_sqrt (show 0 ≤ C / 2 by positivity), Real.sq_sqrt hD,
    mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]

/-- The unit-numerator parameter regime couples the Type II scales. -/
lemma unit_regime_x_le_q_mul_W (x U V q W : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUV : U * V < q - 1)
    (hx : x ≤ U * V ^ 2) (hW : V ≤ W) : x ≤ q * W := by
  have hq : 0 ≤ q := by nlinarith [mul_nonneg hU hV]
  have h1 : U * V ^ 2 ≤ q * V := by nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hUV)) hV]
  have h2 : q * V ≤ q * W := mul_le_mul_of_nonneg_left hW hq
  exact hx.trans (h1.trans h2)

/-- Algebra behind the pointwise Type II bound, valid in the unit regime. -/
lemma typeII_radical_unit (x q W : ℝ) (hx : 0 < x) (hq : 0 < q)
    (hW : 0 < W) (hxqW : x ≤ q * W) :
    Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) ≤
      Real.sqrt (x ^ 2 / (8 * q)) + Real.sqrt (x * W / 4) +
        Real.sqrt (x ^ 2 / (2 * W)) + Real.sqrt (2 * q * x) := by
  have he : (W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x =
      x ^ 2 / (8 * q) + x * W / 4 + x ^ 2 / W + 2 * q * x := by
    field_simp
    <;> ring
  have hc : x ^ 2 / W ≤ 8 * (2 * q * x) := by
    apply (div_le_iff₀ hW).2
    have hm := mul_le_mul_of_nonneg_left hxqW hx.le
    nlinarith [mul_pos hq hx, mul_pos (mul_pos hq hx) hW]
  rw [he]
  simpa only [div_div, mul_comm W 2] using sqrt_four_terms_coupled (x ^ 2 / (8 * q)) (x * W / 4)
    (x ^ 2 / W) (2 * q * x) (by positivity) (by positivity)
    (by positivity) (by positivity) hc

/-- Rounding the exact radical constants to the constants of Theorem 5.1. -/
lemma typeII_round_constants (A B C D L M : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hC : 0 ≤ C) (hD : 0 ≤ D)
    (hL : 0 ≤ L) (hM : 0 ≤ M) :
    (1.1 / 4) * (1 / (2 * Real.sqrt 2) * A + Real.sqrt 2 * B) * L +
      1.1 * ((1 / 2) * C + (1 / Real.sqrt 2) * D) * M ≤
    (0.1 * A + 0.39 * B) * L + (0.55 * C + 0.78 * D) * M := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hsl : (1.414 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hsu : Real.sqrt 2 ≤ (1.415 : ℝ) := by nlinarith
  have hp : 0 < Real.sqrt 2 := by positivity
  have hc1 : (1.1 / 4 : ℝ) * (1 / (2 * Real.sqrt 2)) ≤ 0.1 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have hc2 : (1.1 / 4 : ℝ) * Real.sqrt 2 ≤ 0.39 := by linarith
  have hc3 : (1.1 : ℝ) * (1 / Real.sqrt 2) ≤ 0.78 := by
    rw [mul_one_div, div_le_iff₀ hp]
    linarith
  calc
    _ = ((1.1 / 4) * (1 / (2 * Real.sqrt 2)) * A +
        ((1.1 / 4) * Real.sqrt 2) * B) * L +
        (0.55 * C + (1.1 * (1 / Real.sqrt 2)) * D) * M := by ring
    _ ≤ _ := by gcongr

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51OddHarmonic.lean
section

namespace TaoFivePrimes

lemma odd_reciprocal_range_le (q : ℕ) :
    (∑ k ∈ Finset.range (q + 1), 1 / ((2 * k + 1 : ℕ) : ℝ)) ≤
      1 + (1 / 2 : ℝ) * (harmonic q : ℝ) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.zero_add, Nat.cast_one, div_one]
  have hs : (∑ k ∈ Finset.range q, 1 / ((2 * (k + 1) + 1 : ℕ) : ℝ)) ≤
      (1 / 2 : ℝ) * (harmonic q : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [show (1 / 2 : ℝ) * ((k + 1 : ℕ) : ℝ)⁻¹ =
        1 / (2 * ((k + 1 : ℕ) : ℝ)) by ring]
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
  linarith

/-- A deliberately loose odd harmonic bound, sufficient for q >= 1602. -/
lemma odd_reciprocal_sum_le (q : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ≤ q ∧ Odd d) :
    (∑ d ∈ s, 1 / (d : ℝ)) ≤ 1.5 + 0.5 * Real.log q := by
  let t := (Finset.range (q + 1)).image (fun k => 2 * k + 1)
  have hsub : s ⊆ t := by
    intro d hd
    obtain ⟨hbound, hodd⟩ := hs d hd
    obtain ⟨k, hk⟩ := hodd.exists_bit1
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_range.mpr (by omega), hk.symm⟩
  have he : (∑ d ∈ t, 1 / (d : ℝ)) =
      ∑ k ∈ Finset.range (q + 1), 1 / ((2 * k + 1 : ℕ) : ℝ) := by
    dsimp [t]
    rw [Finset.sum_image]
    intro a ha b hb hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  have hle : (∑ d ∈ s, 1 / (d : ℝ)) ≤ ∑ d ∈ t, 1 / (d : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  rw [he] at hle
  have hH := harmonic_le_one_add_log q
  have hr := odd_reciprocal_range_le q
  linarith

lemma sum_indices_le_square (q : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d < q) :
    (∑ d ∈ s, (d : ℝ)) ≤ (q : ℝ) ^ 2 := by
  have hsub : s ⊆ Finset.range q := fun d hd => Finset.mem_range.mpr (hs d hd)
  have hc : s.card ≤ q := by simpa using Finset.card_le_card hsub
  calc
    _ ≤ ∑ _d ∈ s, (q : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast (hs d hd).le
    _ = (s.card : ℝ) * q := by simp
    _ ≤ (q : ℝ) * q := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)
    _ = _ := by ring

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51TypeITrig.lean
section

namespace TaoFivePrimes

/-- A global quadratic cosecant envelope on the positive half-quadrant. -/
lemma sine_quadratic_envelope (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi / 2) :
    t ^ 2 ≤ (1 + t ^ 2) * Real.sin t ^ 2 := by
  have htB : t ≤ (5 / 3 : ℝ) := by linarith [Real.pi_lt_d2]
  have ht3 : t ^ 2 ≤ 3 := by
    have hb := (sq_le_sq₀ ht.le (by norm_num : (0 : ℝ) ≤ 5 / 3)).2 htB
    norm_num at hb
    linarith
  let r : ℝ := 1 - t ^ 2 / 6
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hs : t * r ≤ Real.sin t := by
    have h := Real.sin_ge_sub_cube ht.le
    dsimp [r]
    nlinarith
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have hR : 1 ≤ (1 + t ^ 2) * r ^ 2 := by
    apply sub_nonneg.mp
    have he : (1 + t ^ 2) * r ^ 2 - 1 = t ^ 2 * (3 - t ^ 2) * (8 - t ^ 2) / 36 := by
      dsimp [r]
      ring
    rw [he]
    have h3 : 0 ≤ 3 - t ^ 2 := by linarith
    have h8 : 0 ≤ 8 - t ^ 2 := by linarith
    positivity
  calc
    t ^ 2 ≤ t ^ 2 * ((1 + t ^ 2) * r ^ 2) := by nlinarith [sq_nonneg t]
    _ = (1 + t ^ 2) * (t * r) ^ 2 := by ring
    _ ≤ (1 + t ^ 2) * Real.sin t ^ 2 :=
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ (mul_nonneg ht.le hr) hsin.le).2 hs) (by positivity)

lemma cosecant_sq_le_inv_sq_add_one (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi / 2) :
    1 / Real.sin t ^ 2 ≤ 1 / t ^ 2 + 1 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have h := sine_quadratic_envelope t ht htpi
  apply (div_le_iff₀ (sq_pos_of_pos hs)).2
  rw [show (1 / t ^ 2 + 1) * Real.sin t ^ 2 =
    ((1 + t ^ 2) * Real.sin t ^ 2) / t ^ 2 by field_simp]
  apply (le_div_iff₀ (sq_pos_of_pos ht)).2
  nlinarith

/-- Transfer the quadratic sine envelope to a weighted reciprocal. -/
lemma weighted_cosecant_envelope (d q t y : ℝ) (hd : 0 < d) (ht : 0 < t)
    (htpi : t ≤ Real.pi / 2) (hy : Real.sin t ≤ y)
    (hscale : d ^ 2 ≤ 0.41 * q ^ 2 * t ^ 2) :
    d / y ^ 2 ≤ 0.41 * q ^ 2 / d + d := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  calc
    _ ≤ d / Real.sin t ^ 2 := div_le_div_of_nonneg_left hd.le
      (sq_pos_of_pos hs) ((sq_le_sq₀ hs.le (hs.le.trans hy)).2 hy)
    _ = d * (1 / Real.sin t ^ 2) := by ring
    _ ≤ d * (1 / t ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left (cosecant_sq_le_inv_sq_add_one t ht htpi) hd.le
    _ = d / t ^ 2 + d := by ring
    _ ≤ _ := by
      suffices h : d / t ^ 2 ≤ 0.41 * q ^ 2 / d by linarith
      apply (div_le_div_iff₀ (sq_pos_of_pos ht) hd).2
      nlinarith

/-- A pointwise bound using the corrected phase endpoint, with numerical
slack that will be recovered by retaining odd summation indices. -/
lemma unit_cosecant_pointwise (alpha beta q d : ℝ) (hq : 1602 ≤ q)
    (hd : 0 < d) (hdq : d ≤ q - 1)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    d / Real.sin (2 * Real.pi * d * alpha) ^ 2 ≤ 0.41 * q ^ 2 / d + d := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q - 1 := by linarith
  let t : ℝ := Real.pi * d * (q - 1) / (2 * q ^ 2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hdqm : d * (q - 1) ≤ q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hdq hqm.le
    nlinarith
  have htpi : t ≤ Real.pi / 2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hdqm Real.pi_pos.le]
  have hbase : (25 / 8 : ℝ) * q ≤ Real.pi * (q - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_d2.le) hqm.le]
  have hscaled : (25 / 16 : ℝ) * d ≤ t * q := by
    have he : t * q = Real.pi * d * (q - 1) / (2 * q) := by
      dsimp [t]
      field_simp
    rw [he]
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_right hbase hd.le]
  have hscale : d ^ 2 ≤ 0.41 * q ^ 2 * t ^ 2 := by
    have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (25 / 16 : ℝ) * d)
      (by positivity : 0 ≤ t * q)).2 hscaled
    nlinarith [sq_nonneg d]
  have hsin : Real.sin t ≤ Real.sin (2 * Real.pi * d * alpha) := by
    convert unit_phase_sine_lower alpha beta q d (by linarith) hd.le hdq hphase hbeta using 1
    congr 1
    dsimp [t]
    ring
  exact weighted_cosecant_envelope d q t _ hd ht htpi hsin hscale

lemma log_denominator_lower (q : ℕ) (hq : 1602 ≤ q) : (6.5 : ℝ) ≤ Real.log q := by
  have hqR : (1024 : ℝ) ≤ q := by exact_mod_cast (show 1024 ≤ q by omega)
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1024) hqR
  have he : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  linarith [Real.log_two_gt_d9]

lemma typeI_numeric_slack (q : ℕ) (hq : 1602 ≤ q) :
    (q : ℝ) ^ 2 * (0.41 * (1.5 + 0.5 * Real.log q) + 1) ≤
      (4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog := log_denominator_lower q hq
  have hpi : Real.pi ^ 2 ≤ 10 := by
    have h := (sq_le_sq₀ Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 3.15)).2 Real.pi_lt_d2.le
    norm_num at h
    linarith
  have hc : (0.4 : ℝ) ≤ 4 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).2
    nlinarith
  have harg : Real.exp 1 * q ≤ 4 * Real.exp 1 * q / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [mul_le_mul_of_nonneg_left Real.pi_lt_four.le
      (show 0 ≤ Real.exp 1 * q by positivity)]
  have hl := Real.log_le_log (show 0 < Real.exp 1 * q by positivity) harg
  rw [Real.log_mul (Real.exp_ne_zero _) hq0.ne', Real.log_exp] at hl
  have hL : 0 ≤ 1 + Real.log q := by linarith
  calc
    _ ≤ (q : ℝ) ^ 2 * (0.4 * (1 + Real.log q)) := by gcongr; linarith
    _ = 0.4 * (q : ℝ) ^ 2 * (1 + Real.log q) := by ring
    _ ≤ _ := by gcongr

/-- The complete odd-index trigonometric sum bound with the constant needed
for (5.7), using the corrected lower phase endpoint. -/
theorem unit_typeI_trigonometric_sum (alpha beta : ℝ) (q : ℕ) (s : Finset ℕ)
    (hq : 1602 ≤ q)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ (q : ℝ) - 1 ∧ Odd d)
    (hphase : 4 * alpha = 1 / (q : ℝ) + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ d ∈ s, (d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) ≤
      (4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hslt : ∀ d ∈ s, d < q := by
    intro d hd
    have hb := (hs d hd).2.1
    exact_mod_cast (show (d : ℝ) < q by linarith)
  have hrec := odd_reciprocal_sum_le q s (fun d hd => ⟨(hslt d hd).le, (hs d hd).2.2⟩)
  have hsum := sum_indices_le_square q s hslt
  calc
    _ ≤ ∑ d ∈ s, (0.41 * (q : ℝ) ^ 2 / (d : ℝ) + d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact unit_cosecant_pointwise alpha beta q d (by exact_mod_cast hq)
        (by exact_mod_cast (hs d hd).1) (hs d hd).2.1 hphase hbeta
    _ = 0.41 * (q : ℝ) ^ 2 * (∑ d ∈ s, 1 / (d : ℝ)) + ∑ d ∈ s, (d : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 0.41 * (q : ℝ) ^ 2 * (1.5 + 0.5 * Real.log q) + (q : ℝ) ^ 2 := by gcongr
    _ = (q : ℝ) ^ 2 * (0.41 * (1.5 + 0.5 * Real.log q) + 1) := by ring
    _ ≤ _ := typeI_numeric_slack q hq

/-- Both signs of the unit numerator give the same squared sine sum. -/
theorem unit_typeI_trigonometric_sum_signed (alpha beta : ℝ) (a : ℤ)
    (q : ℕ) (s : Finset ℕ) (hq : 1602 ≤ q) (ha : a.natAbs = 1)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ (q : ℝ) - 1 ∧ Odd d)
    (hphase : 4 * alpha = (a : ℝ) / (q : ℝ) + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ d ∈ s, (d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) ≤
      (4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  rcases Int.natAbs_eq_iff.mp ha with ha | ha
  · norm_num at ha
    subst a
    exact unit_typeI_trigonometric_sum alpha beta q s hq hs (by simpa using hphase) hbeta
  · norm_num at ha
    subst a
    have hp : 4 * (-alpha) = 1 / (q : ℝ) + (-beta) := by
      norm_num at hphase
      rw [neg_div] at hphase
      linarith
    have h := unit_typeI_trigonometric_sum (-alpha) (-beta) q s hq hs hp (by simpa using hbeta)
    simpa only [mul_neg, Real.sin_neg, neg_sq] using h

lemma unit_regime_denominator_large (U V : ℝ) (q : ℕ)
    (hU : 40 ≤ U) (hV : 40 ≤ V) (hUVq : U * V < (q : ℝ) - 1) : 1602 ≤ q := by
  have h : (1601 : ℝ) < q := by
    nlinarith [mul_nonneg (show 0 ≤ U - 40 by linarith) (show 0 ≤ V - 40 by linarith)]
  have hn : 1601 < q := by exact_mod_cast h
  omega

/-- The full Type I outer-sum assembly. Its pointwise decay hypothesis is
the remaining smoothing obligation and is stated explicitly. -/
theorem unit_typeI_of_pointwise_decay (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ)
    (s : Finset ℕ) (T : ℕ → ℂ)
    (hx : 1 ≤ x) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVq : U * V < (q : ℝ) - 1) (ha : a.natAbs = 1)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ U * V ∧ d.Coprime 2)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hdecay : ∀ d ∈ s, ‖T d‖ ≤ (24 * Real.log (4 * x) / x) *
      ((d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2)) :
    (∑ d ∈ s, ‖T d‖) ≤ (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
      Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hq := unit_regime_denominator_large U V q hU hV hUVq
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog : 0 ≤ Real.log (4 * x) := Real.log_nonneg (by linarith)
  have hK : 0 ≤ 24 * Real.log (4 * x) / x := by positivity
  have htrig := unit_typeI_trigonometric_sum_signed alpha beta a q s hq ha
    (fun d hd => ⟨(hs d hd).1, (hs d hd).2.1.trans hUVq.le,
      Nat.coprime_two_right.mp (hs d hd).2.2⟩) hphase hbeta
  calc
    _ ≤ ∑ d ∈ s, (24 * Real.log (4 * x) / x) *
        ((d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) :=
      Finset.sum_le_sum hdecay
    _ = (24 * Real.log (4 * x) / x) *
        (∑ d ∈ s, (d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (24 * Real.log (4 * x) / x) *
        ((4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi)) :=
      mul_le_mul_of_nonneg_left htrig hK
    _ = _ := by field_simp; ring

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51DiscreteSecondDifference.lean
section

namespace TaoFivePrimes

noncomputable def twistedSecondDifference (z : ℂ) (f : ℤ → ℂ) (n : ℤ) : ℂ :=
  f (n + 2) - 2 * z * f (n + 1) + z ^ 2 * f n

/-- Discrete summation by parts twice, without differentiability assumptions. -/
lemma tsum_twistedSecondDifference (z : ℂ) (f : ℤ → ℂ) (hf : Summable f) :
    (∑' n : ℤ, twistedSecondDifference z f n) = (1 - z) ^ 2 * ∑' n : ℤ, f n := by
  have hf1 : Summable (fun n : ℤ => f (n + 1)) :=
    hf.comp_injective (by intro a b h; change a + 1 = b + 1 at h; omega)
  have hf2 : Summable (fun n : ℤ => f (n + 2)) :=
    hf.comp_injective (by intro a b h; change a + 2 = b + 2 at h; omega)
  have he1 : (∑' n : ℤ, f (n + 1)) = ∑' n : ℤ, f n := (Equiv.addRight 1).tsum_eq f
  have he2 : (∑' n : ℤ, f (n + 2)) = ∑' n : ℤ, f n := (Equiv.addRight 2).tsum_eq f
  simp only [twistedSecondDifference]
  rw [Summable.tsum_add (hf2.sub (hf1.mul_left (2 * z))) (hf.mul_left (z ^ 2)),
    Summable.tsum_sub hf2 (hf1.mul_left (2 * z)), tsum_mul_left, tsum_mul_left, he1, he2]
  ring

/-- The reciprocal-square denominator in the Type I estimate follows from
an l1 bound on discrete second differences. -/
lemma norm_tsum_le_twistedSecondDifference (z : ℂ) (f : ℤ → ℂ)
    (hz : z ≠ 1) (hf : Summable f)
    (hD : Summable (fun n : ℤ => ‖twistedSecondDifference z f n‖)) :
    ‖∑' n : ℤ, f n‖ ≤ (∑' n : ℤ, ‖twistedSecondDifference z f n‖) / ‖1 - z‖ ^ 2 := by
  have h := norm_tsum_le_tsum_norm hD
  rw [tsum_twistedSecondDifference z f hf, norm_mul, norm_pow] at h
  have hp : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))
  apply (le_div_iff₀ (sq_pos_of_pos hp)).2
  nlinarith

lemma norm_exp_gap_sq (theta : ℝ) :
    ‖(1 : ℂ) - Complex.exp (Complex.I * theta)‖ ^ 2 = 4 * Real.sin (theta / 2) ^ 2 := by
  rw [norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, sq_abs]
  ring

lemma norm_tsum_le_sine_second_difference (theta : ℝ) (f : ℤ → ℂ)
    (hs : Real.sin (theta / 2) ≠ 0) (hf : Summable f)
    (hD : Summable (fun n : ℤ => ‖twistedSecondDifference (Complex.exp (Complex.I * theta)) f n‖)) :
    ‖∑' n : ℤ, f n‖ ≤
      (∑' n : ℤ, ‖twistedSecondDifference (Complex.exp (Complex.I * theta)) f n‖) /
        (4 * Real.sin (theta / 2) ^ 2) := by
  have hz : Complex.exp (Complex.I * theta) ≠ 1 := by
    intro h
    have he := norm_exp_gap_sq theta
    rw [h, sub_self, norm_zero] at he
    have hp := sq_pos_of_ne_zero hs
    nlinarith
  have h := norm_tsum_le_twistedSecondDifference _ f hz hf hD
  rwa [norm_exp_gap_sq] at h

/-- Twisted differences remove the geometric phase exactly. -/
lemma twistedSecondDifference_geometric (z : ℂ) (hz : z ≠ 0) (F : ℤ → ℂ) (n : ℤ) :
    twistedSecondDifference z (fun k => F k * z ^ k) n =
      z ^ (n + 2) * (F (n + 2) - 2 * F (n + 1) + F n) := by
  simp only [twistedSecondDifference, zpow_add₀ hz, zpow_ofNat, zpow_one]
  ring

/-- A finite Fourier sum is controlled by the total discrete second
variation of its amplitude. In particular, amplitude corners are allowed. -/
theorem finite_fourier_second_difference_bound (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (F : ℤ → ℂ) (hF : Function.HasFiniteSupport F) :
    ‖∑' n : ℤ, F n * z ^ n‖ ≤
      (∑' n : ℤ, ‖F (n + 2) - 2 * F (n + 1) + F n‖) / ‖1 - z‖ ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hF1 : Function.HasFiniteSupport (fun n : ℤ => F (n + 1)) :=
    hF.fun_comp_of_injective (by intro a b h; change a + 1 = b + 1 at h; omega)
  have hF2 : Function.HasFiniteSupport (fun n : ℤ => F (n + 2)) :=
    hF.fun_comp_of_injective (by intro a b h; change a + 2 = b + 2 at h; omega)
  have hDelta : Function.HasFiniteSupport (fun n : ℤ => F (n + 2) - 2 * F (n + 1) + F n) :=
    (hF2.sub (hF1.fun_comp (show (2 : ℂ) * 0 = 0 by simp))).add hF
  have hG : Summable (fun n : ℤ => F n * z ^ n) :=
    summable_of_hasFiniteSupport (hF.mul_left (fun n => z ^ n))
  have he (n : ℤ) : ‖twistedSecondDifference z (fun k => F k * z ^ k) n‖ =
      ‖F (n + 2) - 2 * F (n + 1) + F n‖ := by
    rw [twistedSecondDifference_geometric z hz0, norm_mul, norm_zpow, hz, one_zpow, one_mul]
  have hD : Summable (fun n : ℤ => ‖twistedSecondDifference z (fun k => F k * z ^ k) n‖) :=
    (summable_of_hasFiniteSupport (hDelta.fun_comp norm_zero)).congr (fun n => (he n).symm)
  have h := norm_tsum_le_twistedSecondDifference z _ hz1 hG hD
  simpa only [he] using h

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51TypeIDiscreteAssembly.lean
section

namespace TaoFivePrimes

lemma positive_unit_sine_pos (alpha beta q d : ℝ) (hq : 1 < q)
    (hd : 0 < d) (hdq : d ≤ q - 1)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    0 < Real.sin (2 * Real.pi * d * alpha) := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q - 1 := by linarith
  let t : ℝ := 2 * Real.pi * d * ((q - 1) / (4 * q ^ 2))
  have ht : 0 < t := by dsimp [t]; positivity
  have he : t = Real.pi * (d * (q - 1)) / (2 * q ^ 2) := by dsimp [t]; ring
  have hb : d * (q - 1) ≤ q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hdq hqm.le
    nlinarith
  have htpi : t ≤ Real.pi / 2 := by
    rw [he]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hb Real.pi_pos.le]
  have hp : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  exact hp.trans_le (unit_phase_sine_lower alpha beta q d hq hd.le hdq hphase hbeta)

lemma unit_sine_ne_zero (alpha beta : ℝ) (a : ℤ) (q : ℕ) (d : ℝ)
    (hq : 1602 ≤ q) (ha : a.natAbs = 1) (hd : 0 < d) (hdq : d ≤ (q : ℝ) - 1)
    (hphase : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    Real.sin (2 * Real.pi * d * alpha) ≠ 0 := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  rcases Int.natAbs_eq_iff.mp ha with ha | ha
  · norm_num at ha
    subst a
    exact (positive_unit_sine_pos alpha beta q d hqR hd hdq (by simpa using hphase) hbeta).ne'
  · norm_num at ha
    subst a
    have hp : 4 * (-alpha) = 1 / (q : ℝ) + (-beta) := by
      norm_num at hphase
      rw [neg_div] at hphase
      linarith
    have h := (positive_unit_sine_pos (-alpha) (-beta) q d hqR hd hdq hp (by simpa using hbeta)).ne'
    simpa only [mul_neg, Real.sin_neg, neg_ne_zero] using h

/-- The Type I bound from a concrete discrete-variation hypothesis.
The unresolved smoothing input is the displayed bound on the amplitude's
second differences; all Fourier cancellation and outer summation are proved. -/
theorem unit_typeI_from_discrete_variation
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ) (s : Finset ℕ) (F : ℕ → ℤ → ℂ)
    (hx : 1 ≤ x) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVq : U * V < (q : ℝ) - 1) (ha : a.natAbs = 1)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ U * V ∧ d.Coprime 2)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hfinite : ∀ d ∈ s, Function.HasFiniteSupport (F d))
    (hvariation : ∀ d ∈ s,
      (∑' n : ℤ, ‖F d (n + 2) - 2 * F d (n + 1) + F d n‖) ≤
        96 * Real.log (4 * x) / x * d) :
    (∑ d ∈ s, ‖∑' n : ℤ, F d n *
      (Complex.exp (Complex.I * ((4 * Real.pi * (d : ℝ) * alpha : ℝ) : ℂ))) ^ n‖) ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
        Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  apply unit_typeI_of_pointwise_decay x alpha beta U V a q s _ hx hU hV hUVq ha hs hphase hbeta
  intro d hd
  have hq := unit_regime_denominator_large U V q hU hV hUVq
  have hsin := unit_sine_ne_zero alpha beta a q d hq ha (by exact_mod_cast (hs d hd).1)
    ((hs d hd).2.1.trans hUVq.le) hphase hbeta
  let theta : ℝ := 4 * Real.pi * d * alpha
  let z : ℂ := Complex.exp (Complex.I * theta)
  have hz : ‖z‖ = 1 := Complex.norm_exp_I_mul_ofReal theta
  have htheta : theta / 2 = 2 * Real.pi * d * alpha := by dsimp [theta]; ring
  have hgap : ‖1 - z‖ ^ 2 = 4 * Real.sin (2 * Real.pi * d * alpha) ^ 2 := by
    rw [show z = Complex.exp (Complex.I * theta) from rfl, norm_exp_gap_sq, htheta]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero, zero_pow (by decide)] at hgap
    nlinarith [sq_pos_of_ne_zero hsin]
  have h := finite_fourier_second_difference_bound z hz hz1 (F d) (hfinite d hd)
  change ‖∑' n : ℤ, F d n * z ^ n‖ ≤ _
  rw [hgap] at h
  calc
    _ ≤ (∑' n : ℤ, ‖F d (n + 2) - 2 * F d (n + 1) + F d n‖) /
        (4 * Real.sin (2 * Real.pi * d * alpha) ^ 2) := h
    _ ≤ (96 * Real.log (4 * x) / x * d) /
        (4 * Real.sin (2 * Real.pi * d * alpha) ^ 2) := by
      apply div_le_div_of_nonneg_right (hvariation d hd)
      positivity
    _ = _ := by ring

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51CutoffAmplitude.lean
section

namespace TaoFivePrimes

lemma eta0_zero_below_quarter {t : ℝ} (ht : t ≤ 1 / 4) : eta0 t = 0 := by
  unfold eta0
  split_ifs with hp
  · have hlog : Real.log (2 * t) ≤ -Real.log 2 := by
      have h := Real.log_le_log (show 0 < 2 * t by positivity)
        (show 2 * t ≤ (1 / 2 : ℝ) by linarith)
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv] at h
      exact h
    have hab : Real.log 2 ≤ |Real.log (2 * t)| := by
      linarith [neg_le_abs (Real.log (2 * t))]
    rw [max_eq_left (by linarith), mul_zero]
  · rfl

lemma eta0_zero_above_one {t : ℝ} (ht : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  rw [if_pos (by linarith)]
  have hl : Real.log 2 ≤ Real.log (2 * t) := Real.log_le_log (by norm_num) (by linarith)
  have hm : Real.log 2 - |Real.log (2 * t)| ≤ 0 := by
    linarith [le_abs_self (Real.log (2 * t))]
  rw [max_eq_left hm, mul_zero]

lemma eta0_lower_piece {t : ℝ} (hlo : 1 / 4 ≤ t) (hhi : t ≤ 1 / 2) :
    eta0 t = 4 * Real.log (4 * t) := by
  have ht : 0 < t := by linarith
  have hneg : Real.log (2 * t) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have he : Real.log 2 + Real.log (2 * t) = Real.log (4 * t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
    congr 1
    ring
  unfold eta0
  rw [if_pos ht, abs_of_nonpos hneg, sub_neg_eq_add, he,
    max_eq_right (Real.log_nonneg (by linarith))]

lemma eta0_upper_piece {t : ℝ} (hlo : 1 / 2 ≤ t) (hhi : t ≤ 1) :
    eta0 t = -4 * Real.log t := by
  have ht : 0 < t := by linarith
  have hpos : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  have he : Real.log 2 - Real.log (2 * t) = -Real.log t := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht.ne']
    ring
  unfold eta0
  rw [if_pos ht, abs_of_nonneg hpos, he,
    max_eq_right (neg_nonneg.mpr (Real.log_nonpos ht.le hhi))]
  ring

/-- Actual odd-lattice amplitude in a Type I inner sum. -/
noncomputable def typeIOddAmplitude (x d : ℝ) (c : ℂ) (n : ℤ) : ℂ :=
  ((Real.log ((2 * n + 1 : ℤ) : ℝ) : ℂ) + c * (Real.log d : ℂ)) *
    (eta0 (d * ((2 * n + 1 : ℤ) : ℝ) / x) : ℂ)

lemma typeIOddAmplitude_finite (x d : ℝ) (c : ℂ) (hx : 0 < x) (hd : 0 < d) :
    Function.HasFiniteSupport (typeIOddAmplitude x d c) := by
  apply (Set.finite_Icc (0 : ℤ) ⌈x / d⌉).subset
  intro n hn
  by_contra hnot
  have hz : typeIOddAmplitude x d c n = 0 := by
    unfold typeIOddAmplitude
    suffices he : eta0 (d * ((2 * n + 1 : ℤ) : ℝ) / x) = 0 by rw [he]; simp
    simp only [Set.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with hlo | hhi
    · apply eta0_zero_below_quarter
      have hn0 : n ≤ -1 := by omega
      have hy : ((2 * n + 1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (show 2 * n + 1 ≤ 0 by omega)
      have hh : d * ((2 * n + 1 : ℤ) : ℝ) / x ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hd.le hy) hx.le
      linarith
    · apply eta0_zero_above_one
      have hceil : x / d ≤ (⌈x / d⌉ : ℤ) := Int.le_ceil _
      have hnR : ((⌈x / d⌉ : ℤ) : ℝ) < n := by exact_mod_cast hhi
      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (div_pos hx hd) (hceil.trans hnR.le)
      have hy : x / d ≤ ((2 * n + 1 : ℤ) : ℝ) := by push_cast; linarith
      apply (le_div_iff₀ hx).2
      have hh := (div_le_iff₀ hd).mp hy
      nlinarith
  exact hn hz

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51OddFourierBridge.lean
section

namespace TaoFivePrimes

lemma expCircle_odd_geometric (alpha d : ℝ) (n : ℤ) :
    expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ)) =
      expCircle (alpha * d) *
        (Complex.exp (Complex.I * ((4 * Real.pi * d * alpha : ℝ) : ℂ))) ^ n := by
  unfold expCircle
  rw [← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma expCircle_norm_unit (t : ℝ) : ‖expCircle t‖ = 1 := by
  unfold expCircle
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
    Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) by push_cast; ring]
  exact Complex.norm_exp_I_mul_ofReal _

/-- Removing the harmless unit phase is exact, for every integer-indexed amplitude. -/
lemma norm_odd_fourier_eq_geometric (alpha d : ℝ) (F : ℤ → ℂ) :
    ‖∑' n : ℤ, F n * expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ))‖ =
      ‖∑' n : ℤ, F n *
        (Complex.exp (Complex.I * ((4 * Real.pi * d * alpha : ℝ) : ℂ))) ^ n‖ := by
  simp_rw [expCircle_odd_geometric, mul_left_comm (F _) (expCircle (alpha * d))]
  rw [tsum_mul_left, norm_mul, expCircle_norm_unit, one_mul]

/-- Actual odd-lattice Type I sum: no smoothness hypothesis is used. -/
theorem typeI_odd_sum_second_difference_bound (x d alpha : ℝ) (c : ℂ)
    (hx : 0 < x) (hd : 0 < d) (hsin : Real.sin (2 * Real.pi * d * alpha) ≠ 0) :
    ‖∑' n : ℤ, typeIOddAmplitude x d c n *
      expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ))‖ ≤
    (∑' n : ℤ, ‖typeIOddAmplitude x d c (n + 2) -
      2 * typeIOddAmplitude x d c (n + 1) + typeIOddAmplitude x d c n‖) /
      (4 * Real.sin (2 * Real.pi * d * alpha) ^ 2) := by
  rw [norm_odd_fourier_eq_geometric]
  let theta : ℝ := 4 * Real.pi * d * alpha
  let z : ℂ := Complex.exp (Complex.I * (theta : ℂ))
  have hz : ‖z‖ = 1 := Complex.norm_exp_I_mul_ofReal theta
  have hgap : ‖1 - z‖ ^ 2 = 4 * Real.sin (2 * Real.pi * d * alpha) ^ 2 := by
    dsimp [z]
    rw [norm_exp_gap_sq, show theta / 2 = 2 * Real.pi * d * alpha by dsimp [theta]; ring]
  have hz1 : z ≠ 1 := by
    intro he
    rw [he, sub_self, norm_zero, zero_pow (by decide)] at hgap
    nlinarith [sq_pos_of_ne_zero hsin]
  have h := finite_fourier_second_difference_bound z hz hz1
    (typeIOddAmplitude x d c) (typeIOddAmplitude_finite x d c hx hd)
  rw [hgap] at h
  exact h

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51AmplitudeCalculus.lean
section

namespace TaoFivePrimes

/-- The logarithmic coefficient never exceeds log x on the cutoff support. -/
lemma typeI_log_coefficient_bound (x d y : ℝ) (c : ℂ)
    (hd : 1 ≤ d) (hy : 1 ≤ y) (hxy : d * y ≤ x) (hc : ‖c‖ ≤ 1) :
    ‖(Real.log y : ℂ) + c * (Real.log d : ℂ)‖ ≤ Real.log x := by
  have hd0 : 0 < d := by linarith
  have hy0 : 0 < y := by linarith
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  calc
    _ ≤ ‖(Real.log y : ℂ)‖ + ‖c * (Real.log d : ℂ)‖ := norm_add_le _ _
    _ = Real.log y + ‖c‖ * Real.log d := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hly, abs_of_nonneg hld]
    _ ≤ Real.log y + Real.log d := by nlinarith
    _ = Real.log (d * y) := by rw [Real.log_mul hd0.ne' hy0.ne']; ring
    _ ≤ Real.log x := Real.log_le_log (mul_pos hd0 hy0) hxy

/-- Each smooth piece of the logarithmic amplitude has this universal form. -/
lemma log_product_hasDerivAt (y : ℝ) (hy : y ≠ 0) (b k : ℂ) :
    HasDerivAt (fun t : ℝ => 4 * ((Real.log t : ℂ) + k) * ((Real.log t : ℂ) + b))
      (4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b + k)) y := by
  have h := (((Real.hasDerivAt_log hy).ofReal_comp.add_const k).const_mul 4).mul
    ((Real.hasDerivAt_log hy).ofReal_comp.add_const b)
  convert h using 1 <;> first | rfl | (simp only [Complex.ofReal_inv, div_eq_mul_inv]; ring)

lemma log_product_derivative_hasDerivAt (y : ℝ) (hy : y ≠ 0) (b k : ℂ) :
    HasDerivAt (fun t : ℝ => 4 / (t : ℂ) * (2 * (Real.log t : ℂ) + b + k))
      (4 / (y : ℂ) ^ 2 * (2 - 2 * (Real.log y : ℂ) - b - k)) y := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have h := ((hasDerivAt_const y (4 : ℂ)).div
    (hasDerivAt_id y).ofReal_comp hyC).mul
      ((((Real.hasDerivAt_log hy).ofReal_comp.const_mul 2).add_const b).add_const k)
  convert h using 1 <;> first | rfl | (simp only [Pi.div_apply, id_eq,
    Complex.ofReal_one, Complex.ofReal_inv]; field_simp; ring)

/-- A uniform majorant for the curvature of either logarithmic piece.
Here L is the logarithm in the cutoff and g is the logarithmic coefficient. -/
lemma typeI_curvature_majorant (y X L : ℝ) (g : ℂ) (hy : 0 < y)
    (hg : ‖g‖ ≤ X) (hL : |L| ≤ 3 / 4) :
    ‖(4 / (y : ℂ) ^ 2) * (2 - g - (L : ℂ))‖ ≤ (4 * X + 11) / y ^ 2 := by
  have hb : ‖(2 : ℂ) - g - (L : ℂ)‖ ≤ 2 + X + 3 / 4 := by
    calc
      _ ≤ ‖(2 : ℂ) - g‖ + ‖(L : ℂ)‖ := norm_sub_le _ _
      _ ≤ (‖(2 : ℂ)‖ + ‖g‖) + ‖(L : ℂ)‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ 2 + X + 3 / 4 := by
        norm_num [Complex.norm_real, Real.norm_eq_abs]
        linarith
  have he : ‖(4 : ℂ) / (y : ℂ) ^ 2‖ = 4 / y ^ 2 := by
    simp [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  rw [norm_mul, he]
  calc
    _ ≤ (4 / y ^ 2) * (2 + X + 3 / 4) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Exact integral of the regular-curvature majorant over the cutoff support. -/
lemma typeI_curvature_majorant_integral (r X : ℝ) (hr : 0 < r) :
    (∫ y in r / 4..r, (4 * X + 11) / y ^ 2) = (12 * X + 33) / r := by
  have hz : (0 : ℝ) ∉ Set.uIcc (r / 4) r := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hi := integral_zpow (a := r / 4) (b := r) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, hz⟩)
  norm_num at hi
  have he (y : ℝ) : (4 * X + 11) / y ^ 2 = (4 * X + 11) * y ^ (-2 : ℤ) := by
    simp [zpow_neg, div_eq_mul_inv]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  simp only [zpow_neg, zpow_ofNat]
  rw [hi]
  field_simp
  ring

/-- The three slope jumps contribute at most 36 log(x)/r.
Together with the regular-curvature integral there is room in 48 log(4x)/r.
The passage from this budget to discrete variation is a separate obligation. -/
lemma typeI_curvature_and_jump_budget (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    (12 * Real.log x + 33) / r + 36 * Real.log x / r ≤
      48 * Real.log (4 * x) / r := by
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx.ne', hl4]
  apply (le_div_iff₀ hr).2
  field_simp
  nlinarith [Real.log_two_gt_d9]

lemma typeI_amplitude_lower_formula (r d y : ℝ) (c : ℂ)
    (hr : 0 < r) (hy : 0 < y) (hlo : 1 / 4 ≤ y / r) (hhi : y / r ≤ 1 / 2) :
    ((Real.log y : ℂ) + c * (Real.log d : ℂ)) * (eta0 (y / r) : ℂ) =
      4 * ((Real.log y : ℂ) + (Real.log (4 / r) : ℂ)) *
        ((Real.log y : ℂ) + c * (Real.log d : ℂ)) := by
  rw [eta0_lower_piece hlo hhi,
    show 4 * (y / r) = y * (4 / r) by ring,
    Real.log_mul hy.ne' (by positivity : (4 : ℝ) / r ≠ 0)]
  push_cast
  ring

lemma typeI_amplitude_upper_formula (r d y : ℝ) (c : ℂ)
    (hr : 0 < r) (hy : 0 < y) (hlo : 1 / 2 ≤ y / r) (hhi : y / r ≤ 1) :
    ((Real.log y : ℂ) + c * (Real.log d : ℂ)) * (eta0 (y / r) : ℂ) =
      -4 * ((Real.log y : ℂ) - (Real.log r : ℂ)) *
        ((Real.log y : ℂ) + c * (Real.log d : ℂ)) := by
  rw [eta0_upper_piece hlo hhi, Real.log_div hy.ne' hr.ne']
  push_cast
  ring

/-- The slope jumps at r/4, r/2, and r have weights 16, 16, and 4. -/
lemma typeI_jump_norm_budget (r X : ℝ) (A B C : ℂ) (hr : 0 < r)
    (hA : ‖A‖ ≤ X) (hB : ‖B‖ ≤ X) (hC : ‖C‖ ≤ X) :
    ‖(16 / (r : ℂ)) * A‖ + ‖(16 / (r : ℂ)) * B‖ + ‖(4 / (r : ℂ)) * C‖ ≤
      36 * X / r := by
  have h16 : ‖(16 : ℂ) / (r : ℂ)‖ = 16 / r := by
    simp [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have h4 : ‖(4 : ℂ) / (r : ℂ)‖ = 4 / r := by
    simp [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  simp only [norm_mul, h16, h4]
  calc
    _ ≤ (16 / r) * X + (16 / r) * X + (4 / r) * X := by gcongr
    _ = _ := by ring

/-- The exact one-sided slope at the left endpoint. -/
lemma typeI_left_endpoint_slope (r : ℝ) (hr : 0 < r) (b : ℂ) :
    4 / ((r / 4 : ℝ) : ℂ) *
      (2 * (Real.log (r / 4) : ℂ) + b + (Real.log (4 / r) : ℂ)) =
      (16 / (r : ℂ)) * ((Real.log (r / 4) : ℂ) + b) := by
  rw [Real.log_div hr.ne' (by norm_num), Real.log_div (by norm_num) hr.ne']
  push_cast
  field_simp
  ring

/-- The exact slope jump at the interior corner. -/
lemma typeI_middle_slope_jump (r : ℝ) (hr : 0 < r) (b : ℂ) :
    (-4 / ((r / 2 : ℝ) : ℂ) * (2 * (Real.log (r / 2) : ℂ) + b - (Real.log r : ℂ))) -
      (4 / ((r / 2 : ℝ) : ℂ) *
        (2 * (Real.log (r / 2) : ℂ) + b + (Real.log (4 / r) : ℂ))) =
      (-16 / (r : ℂ)) * ((Real.log (r / 2) : ℂ) + b) := by
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [Real.log_div hr.ne' (by norm_num), Real.log_div (by norm_num) hr.ne', hl4]
  push_cast
  field_simp
  ring

lemma typeI_right_endpoint_slope (r : ℝ) (b : ℂ) :
    -4 / (r : ℂ) * (2 * (Real.log r : ℂ) + b - (Real.log r : ℂ)) =
      (-4 / (r : ℂ)) * ((Real.log r : ℂ) + b) := by ring

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51VariationTransfer.lean
section

namespace TaoFivePrimes

open MeasureTheory

/-- Transfer a bound for sampled first differences of an integrable slope
to second differences of its primitive, without differentiability at corners.
The step identity is the integral form of absolute continuity. -/
theorem second_difference_from_integrated_slope
    (F g : ℝ → ℂ) (a V : ℝ) (N : ℕ)
    (hint : ∀ n : ℕ, IntervalIntegrable (fun t => g (a + 2 * n + t)) volume 0 2)
    (hstep : ∀ n : ℕ, F (a + 2 * (n + 1)) - F (a + 2 * n) =
      ∫ t in (0 : ℝ)..2, g (a + 2 * n + t))
    (hvar : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      (∑ n ∈ Finset.range N, ‖g (a + 2 * (n + 1) + t) - g (a + 2 * n + t)‖) ≤ V) :
    (∑ n ∈ Finset.range N,
      ‖F (a + 2 * (n + 2)) - 2 * F (a + 2 * (n + 1)) + F (a + 2 * n)‖) ≤ 2 * V := by
  let H (n : ℕ) (t : ℝ) := g (a + 2 * (n + 1) + t) - g (a + 2 * n + t)
  have hH (n : ℕ) : IntervalIntegrable (H n) volume 0 2 := by
    simpa [H, Nat.cast_add, Nat.cast_one] using (hint (n + 1)).sub (hint n)
  have he (n : ℕ) : F (a + 2 * (n + 2)) - 2 * F (a + 2 * (n + 1)) + F (a + 2 * n) =
      ∫ t in (0 : ℝ)..2, H n t := by
    have hnext := hstep (n + 1)
    push_cast at hnext
    have hcur := hstep n
    have hsub := intervalIntegral.integral_sub (hint (n + 1)) (hint n)
    push_cast at hsub
    dsimp [H]
    rw [show (fun t : ℝ => g (a + 2 * (↑n + 1) + t) - g (a + 2 * ↑n + t)) =
      (fun t : ℝ => g (a + 2 * (↑n + 1) + t) - g (a + 2 * ↑n + t)) from rfl]
    rw [hsub, ← hnext, ← hcur]
    congr 1 <;> ring
  calc
    _ ≤ ∑ n ∈ Finset.range N, ∫ t in (0 : ℝ)..2, ‖H n t‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [he]
      exact intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ t in (0 : ℝ)..2, ∑ n ∈ Finset.range N, ‖H n t‖ := by
      symm
      exact intervalIntegral.integral_finsetSum (fun n hn => (hH n).norm)
    _ ≤ ∫ t in (0 : ℝ)..2, V := by
      have hsum : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N, ‖H n t‖) volume 0 2 := by
        have hs (s : Finset ℕ) : IntervalIntegrable (fun t => ∑ n ∈ s, ‖H n t‖) volume 0 2 := by
          induction s using Finset.induction with
          | empty => simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 2)
          | @insert n s hn ih =>
              simpa only [Finset.sum_insert hn] using (hH n).norm.add ih
        exact hs (Finset.range N)
      apply intervalIntegral.integral_mono_on (by norm_num)
        hsum intervalIntegrable_const
      exact hvar
    _ = 2 * V := by simp [mul_comm]

/-- Mathlib's bounded-variation quantity directly supplies the sampled bound. -/
theorem second_difference_from_bounded_variation
    (F g : ℝ → ℂ) (a V : ℝ) (N : ℕ) (hV : 0 ≤ V)
    (hint : ∀ n : ℕ, IntervalIntegrable (fun t => g (a + 2 * n + t)) volume 0 2)
    (hstep : ∀ n : ℕ, F (a + 2 * (n + 1)) - F (a + 2 * n) =
      ∫ t in (0 : ℝ)..2, g (a + 2 * n + t))
    (hvar : eVariationOn g Set.univ ≤ ENNReal.ofReal V) :
    (∑ n ∈ Finset.range N,
      ‖F (a + 2 * (n + 2)) - 2 * F (a + 2 * (n + 1)) + F (a + 2 * n)‖) ≤ 2 * V := by
  apply second_difference_from_integrated_slope F g a V N hint hstep
  intro t ht
  have hu : Monotone (fun n : ℕ => a + 2 * (n : ℝ) + t) := by
    intro m n hmn
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have h := (eVariationOn.sum_le (f := g) (s := Set.univ) (n := N)
    hu (fun _ => Set.mem_univ _)).trans hvar
  simp only [edist_dist, dist_eq_norm, Nat.cast_add, Nat.cast_one] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n hn => norm_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hV).mp h

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51VariationControl.lean
section

namespace TaoFivePrimes

/-- A real-valued increment budget controls the full metric variation. -/
theorem variation_le_of_increment_control (g : ℝ → ℂ) (B : ℝ → ℝ)
    (s : Set ℝ) (V : ℝ)
    (hstep : ∀ u ∈ s, ∀ v ∈ s, u ≤ v → ‖g v - g u‖ ≤ B v - B u)
    (hrange : ∀ u ∈ s, ∀ v ∈ s, B v - B u ≤ V) :
    eVariationOn g s ≤ ENNReal.ofReal V := by
  apply iSup_le
  rintro ⟨N, u, hu, hus⟩
  simp only [edist_dist, dist_eq_norm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n hn => norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ n ∈ Finset.range N, (B (u (n + 1)) - B (u n)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hstep _ (hus n) _ (hus (n + 1)) (hu (Nat.le_succ n))
    _ = B (u N) - B (u 0) := by
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih]; ring
    _ ≤ V := hrange _ (hus 0) _ (hus N)

/-- A single right-continuous slope jump contributes at most its norm. -/
theorem variation_step_le (a : ℝ) (z : ℂ) :
    eVariationOn (fun t : ℝ => if t < a then 0 else z) Set.univ ≤ ENNReal.ofReal ‖z‖ := by
  apply variation_le_of_increment_control _ (fun t : ℝ => if t < a then 0 else ‖z‖)
  · intro u hu v hv huv
    split_ifs <;> simp_all <;> linarith
  · intro u hu v hv
    split_ifs <;> simp_all <;> linarith [norm_nonneg z]

/-- Summing two finite variation budgets preserves their explicit constants. -/
theorem variation_add_budget (f g : ℝ → ℂ) (s : Set ℝ) (V W : ℝ)
    (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hf : eVariationOn f s ≤ ENNReal.ofReal V)
    (hg : eVariationOn g s ≤ ENNReal.ofReal W) :
    eVariationOn (fun t => f t + g t) s ≤ ENNReal.ofReal (V + W) := by
  apply iSup_le
  rintro ⟨N, u, hu, hus⟩
  have hf' := (eVariationOn.sum_le (f := f) (n := N) hu hus).trans hf
  have hg' := (eVariationOn.sum_le (f := g) (n := N) hu hus).trans hg
  simp only [edist_dist, dist_eq_norm] at hf' hg' ⊢
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n hn => norm_nonneg _)] at hf' hg' ⊢
  have hfR := (ENNReal.ofReal_le_ofReal_iff hV).mp hf'
  have hgR := (ENNReal.ofReal_le_ofReal_iff hW).mp hg'
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ n ∈ Finset.range N, (‖f (u (n + 1)) - f (u n)‖ + ‖g (u (n + 1)) - g (u n)‖) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [show f (u (n + 1)) + g (u (n + 1)) - (f (u n) + g (u n)) =
        (f (u (n + 1)) - f (u n)) + (g (u (n + 1)) - g (u n)) by ring]
      exact norm_add_le _ _
    _ ≤ V + W := by rw [Finset.sum_add_distrib]; exact add_le_add hfR hgR

/-- Variable derivative bounds control increments, using one-sided mean value
comparison rather than a smoothness assumption at interval endpoints. -/
theorem norm_sub_le_of_derivative_control (g g' : ℝ → ℂ) (B B' : ℝ → ℝ)
    (a b : ℝ) (hab : a ≤ b)
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hB : ∀ t ∈ Set.Icc a b, HasDerivAt B (B' t) t)
    (hbound : ∀ t ∈ Set.Icc a b, ‖g' t‖ ≤ B' t) :
    ‖g b - g a‖ ≤ B b - B a := by
  apply image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun t => g t - g a) (f' := g')
    (B := fun t => B t - B a) (B' := B') (a := a) (b := b)
    (fun t ht => ((hg t ht).sub_const (g a)).continuousAt.continuousWithinAt)
    (fun t ht => ((hg t ⟨ht.1, ht.2.le⟩).sub_const (g a)).hasDerivWithinAt)
    (by simp)
    (fun t ht => ((hB t ht).sub_const (B a)).continuousAt.continuousWithinAt)
    (fun t ht => ((hB t ⟨ht.1, ht.2.le⟩).sub_const (B a)).hasDerivWithinAt)
    (fun t ht => hbound t ⟨ht.1, ht.2.le⟩)
  exact ⟨hab, le_rfl⟩

/-- Smooth-piece variation with a nonconstant, integrable curvature budget. -/
theorem variation_interval_of_derivative_control (g g' : ℝ → ℂ) (B B' : ℝ → ℝ)
    (a b : ℝ)
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hB : ∀ t ∈ Set.Icc a b, HasDerivAt B (B' t) t)
    (hbound : ∀ t ∈ Set.Icc a b, ‖g' t‖ ≤ B' t)
    (hmono : MonotoneOn B (Set.Icc a b)) :
    eVariationOn g (Set.Icc a b) ≤ ENNReal.ofReal (B b - B a) := by
  apply variation_le_of_increment_control g B
  · intro u hu v hv huv
    have hsub : Set.Icc u v ⊆ Set.Icc a b := by
      intro t ht
      exact ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩
    exact norm_sub_le_of_derivative_control g g' B B' u v huv
      (fun t ht => hg t (hsub ht)) (fun t ht => hB t (hsub ht))
      (fun t ht => hbound t (hsub ht))
  · intro u hu v hv
    have hab : a ≤ b := hu.1.trans hu.2
    have h1 := hmono hu ⟨hab, le_rfl⟩ hu.2
    have h2 := hmono ⟨le_rfl, hab⟩ hv hv.1
    have h3 := hmono hv ⟨hab, le_rfl⟩ hv.2
    have h4 := hmono ⟨le_rfl, hab⟩ hu hu.1
    linarith

lemma variation_sub_constant (f : ℝ → ℂ) (s : Set ℝ) (z : ℂ) :
    eVariationOn (fun t => f t - z) s = eVariationOn f s := by
  simp only [eVariationOn, edist_dist, dist_eq_norm, sub_sub_sub_cancel_right]

/-- Clamping a smooth piece to its interval does not increase variation. -/
lemma variation_clamp_le (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b) :
    eVariationOn (fun t => f (max a (min b t))) Set.univ ≤ eVariationOn f (Set.Icc a b) := by
  apply eVariationOn.comp_le_of_monotoneOn f
  · intro u hu v hv huv
    exact max_le_max_left a (min_le_min_left b huv)
  · intro t ht
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

noncomputable def joinedSlope (L R : ℝ → ℂ) (a b c y : ℝ) : ℂ :=
  if y < a then 0 else if y < b then L y else if y < c then R y else 0

/-- Clamped smooth pieces plus their three jumps give the exact zero extension. -/
lemma joinedSlope_decomposition (L R : ℝ → ℂ) (a b c y : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    joinedSlope L R a b c y =
      (L (max a (min b y)) - L a) + (R (max b (min c y)) - R b) +
      (if y < a then 0 else L a) + (if y < b then 0 else R b - L b) +
      (if y < c then 0 else -R c) := by
  unfold joinedSlope
  by_cases ha : y < a
  · have hb : y < b := ha.trans_le hab
    have hc : y < c := hb.trans_le hbc
    simp [ha, hb, hc, min_eq_right hb.le, min_eq_right hc.le,
      max_eq_left ha.le, max_eq_left hb.le]
  · have hay : a ≤ y := le_of_not_gt ha
    by_cases hb : y < b
    · have hc : y < c := hb.trans_le hbc
      simp [ha, hb, hc, min_eq_right hb.le, min_eq_right hc.le,
        max_eq_right hay, max_eq_left hb.le]
    · have hby : b ≤ y := le_of_not_gt hb
      by_cases hc : y < c
      · simp only [ha, hb, hc, ↓reduceIte, min_eq_left hby, max_eq_right hab,
          min_eq_right hc.le, max_eq_right hby]
        ring
      · have hcy : c ≤ y := le_of_not_gt hc
        simp only [ha, hb, hc, ↓reduceIte, min_eq_left hby, max_eq_right hab,
          min_eq_left hcy, max_eq_right hbc]
        ring

theorem joinedSlope_variation_budget (L R : ℝ → ℂ) (a b c V W : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hL : eVariationOn L (Set.Icc a b) ≤ ENNReal.ofReal V)
    (hR : eVariationOn R (Set.Icc b c) ≤ ENNReal.ofReal W) :
    eVariationOn (joinedSlope L R a b c) Set.univ ≤
      ENNReal.ofReal (V + W + ‖L a‖ + ‖R b - L b‖ + ‖R c‖) := by
  have h1 : eVariationOn (fun y => L (max a (min b y)) - L a) Set.univ ≤ ENNReal.ofReal V := by
    rw [variation_sub_constant]
    exact (variation_clamp_le L a b hab).trans hL
  have h2 : eVariationOn (fun y => R (max b (min c y)) - R b) Set.univ ≤ ENNReal.ofReal W := by
    rw [variation_sub_constant]
    exact (variation_clamp_le R b c hbc).trans hR
  have h12 := variation_add_budget _ _ Set.univ V W hV hW h1 h2
  have h3 := variation_add_budget _ _ Set.univ (V + W) ‖L a‖ (by positivity)
    (norm_nonneg _) h12 (variation_step_le a (L a))
  have h4 := variation_add_budget _ _ Set.univ (V + W + ‖L a‖) ‖R b - L b‖ (by positivity)
    (norm_nonneg _) h3 (variation_step_le b (R b - L b))
  have h5 := variation_add_budget _ _ Set.univ (V + W + ‖L a‖ + ‖R b - L b‖) ‖-R c‖ (by positivity)
    (norm_nonneg _) h4 (variation_step_le c (-R c))
  have he := funext (fun y => joinedSlope_decomposition L R a b c y hab hbc)
  rw [he]
  simpa only [norm_neg] using h5

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51SlopeVariation.lean
section

namespace TaoFivePrimes

/-- Variation of one logarithmic slope piece, with its inverse-square
curvature integrated exactly rather than replaced by a uniform bound. -/
theorem log_slope_variation_bound (a b X k : ℝ) (c : ℂ)
    (ha : 0 < a) (hX : 0 ≤ X)
    (hcoef : ∀ y ∈ Set.Icc a b, ‖(Real.log y : ℂ) + c‖ ≤ X)
    (hcut : ∀ y ∈ Set.Icc a b, |Real.log y + k| ≤ 3 / 4) :
    eVariationOn (fun y : ℝ => 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c + (k : ℂ)))
      (Set.Icc a b) ≤ ENNReal.ofReal ((4 * X + 11) * (a⁻¹ - b⁻¹)) := by
  let C : ℝ := 4 * X + 11
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hB (y : ℝ) (hy : y ≠ 0) :
      HasDerivAt (fun t : ℝ => -C / t) (C / y ^ 2) y := by
    have h := (hasDerivAt_const y (-C)).div (hasDerivAt_id y) hy
    convert h using 1 <;> first | rfl | simp
  have h := variation_interval_of_derivative_control
    (fun y : ℝ => 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c + (k : ℂ)))
    (fun y : ℝ => 4 / (y : ℂ) ^ 2 * (2 - 2 * (Real.log y : ℂ) - c - (k : ℂ)))
    (fun y : ℝ => -C / y) (fun y : ℝ => C / y ^ 2) a b
    (fun y hy => log_product_derivative_hasDerivAt y (ne_of_gt (ha.trans_le hy.1)) c k)
    (fun y hy => hB y (ne_of_gt (ha.trans_le hy.1)))
    (by
      intro y hy
      have hh := typeI_curvature_majorant y X (Real.log y + k) ((Real.log y : ℂ) + c)
        (ha.trans_le hy.1) (hcoef y hy) (hcut y hy)
      convert hh using 1 <;> first | rfl | (push_cast; congr 1; ring))
    (by
      intro u hu v hv huv
      dsimp
      rw [neg_div, neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_left hC (ha.trans_le hu.1) huv))
  convert h using 1
  congr 1
  dsimp [C]
  ring

lemma abs_log_ratio_short (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ 2 * a) :
    |Real.log b - Real.log a| ≤ 3 / 4 := by
  have hb : 0 < b := ha.trans_le hab
  have hlog0 : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr (Real.log_le_log ha hab)
  rw [abs_of_nonneg hlog0, ← Real.log_div hb.ne' ha.ne']
  have hlog2 := Real.log_le_log (div_pos hb ha) ((div_le_iff₀ ha).mpr (by linarith : b ≤ 2 * a))
  linarith [Real.log_two_lt_d9]

lemma lower_cutoff_log_bound (r y : ℝ) (hr : 0 < r) (hy : y ∈ Set.Icc (r / 4) (r / 2)) :
    |Real.log y + Real.log (4 / r)| ≤ 3 / 4 := by
  have h := abs_log_ratio_short (r / 4) y (by positivity) hy.1 (by linarith [hy.2])
  have he : Real.log (4 / r) = -Real.log (r / 4) := by
    rw [Real.log_div (by norm_num) hr.ne', Real.log_div hr.ne' (by norm_num)]
    ring
  simpa only [he, sub_eq_add_neg] using h

lemma upper_cutoff_log_bound (r y : ℝ) (hr : 0 < r) (hy : y ∈ Set.Icc (r / 2) r) :
    |Real.log y + -Real.log r| ≤ 3 / 4 := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity : 0 < r / 2) hy.1
  have h := abs_log_ratio_short y r hy0 hy.2 (by linarith [hy.1])
  simpa only [← sub_eq_add_neg, abs_sub_comm] using h

lemma variation_neg (f : ℝ → ℂ) (s : Set ℝ) :
    eVariationOn (fun y => -f y) s = eVariationOn f s := by
  simp only [eVariationOn, edist_dist, dist_eq_norm, neg_sub_neg, norm_sub_rev]

noncomputable def typeIPiecewiseSlope (r d : ℝ) (c : ℂ) : ℝ → ℂ :=
  joinedSlope
    (fun y => 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) + (Real.log (4 / r) : ℂ)))
    (fun y => -4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) - (Real.log r : ℂ)))
    (r / 4) (r / 2) r

/-- The actual zero-extended piecewise slope has the required variation budget. -/
theorem typeI_piecewise_slope_variation (r d : ℝ) (c : ℂ)
    (hr : 4 ≤ r) (hd : 1 ≤ d) (hc : ‖c‖ ≤ 1) :
    eVariationOn (typeIPiecewiseSlope r d c) Set.univ ≤
      ENNReal.ofReal (48 * Real.log (4 * (d * r)) / r) := by
  have hr0 : 0 < r := by linarith
  have hd0 : 0 < d := by linarith
  let X := Real.log (d * r)
  let C := 4 * X + 11
  let b0 : ℂ := c * (Real.log d : ℂ)
  let L (y : ℝ) := 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b0 + (Real.log (4 / r) : ℂ))
  let R (y : ℝ) := -4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b0 - (Real.log r : ℂ))
  have hX : 0 ≤ X := Real.log_nonneg (by nlinarith)
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hcoef (y : ℝ) (hy : y ∈ Set.Icc (r / 4) r) : ‖(Real.log y : ℂ) + b0‖ ≤ X := by
    apply typeI_log_coefficient_bound (d * r) d y c hd (by linarith [hy.1]) _ hc
    exact mul_le_mul_of_nonneg_left hy.2 hd0.le
  have hL : eVariationOn L (Set.Icc (r / 4) (r / 2)) ≤ ENNReal.ofReal (2 * C / r) := by
    have h := log_slope_variation_bound (r / 4) (r / 2) X (Real.log (4 / r)) b0
      (by positivity) hX (fun y hy => hcoef y ⟨hy.1, by linarith [hy.2]⟩)
      (fun y hy => lower_cutoff_log_bound r y hr0 hy)
    convert h using 1
    congr 1
    dsimp [C]
    field_simp
    ring
  have hR : eVariationOn R (Set.Icc (r / 2) r) ≤ ENNReal.ofReal (C / r) := by
    let P (y : ℝ) := 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b0 + ((-Real.log r : ℝ) : ℂ))
    have he : R = fun y => -P y := by
      funext y
      dsimp [R, P]
      push_cast
      ring
    rw [he, variation_neg]
    have h := log_slope_variation_bound (r / 2) r X (-Real.log r) b0
      (by positivity) hX (fun y hy => hcoef y ⟨by linarith [hy.1], hy.2⟩)
      (fun y hy => upper_cutoff_log_bound r y hr0 hy)
    convert h using 1
    congr 1
    dsimp [C]
    field_simp
    ring
  have hj : ‖L (r / 4)‖ + ‖R (r / 2) - L (r / 2)‖ + ‖R r‖ ≤ 36 * X / r := by
    have h := typeI_jump_norm_budget r X
      ((Real.log (r / 4) : ℂ) + b0) ((Real.log (r / 2) : ℂ) + b0)
      ((Real.log r : ℂ) + b0) hr0
      (hcoef _ ⟨le_rfl, by linarith⟩) (hcoef _ ⟨by linarith, by linarith⟩)
      (hcoef _ ⟨by linarith, le_rfl⟩)
    dsimp [L, R]
    rw [typeI_left_endpoint_slope r hr0 b0, typeI_middle_slope_jump r hr0 b0,
      typeI_right_endpoint_slope r b0]
    simpa only [neg_div, neg_mul, norm_neg] using h
  have h := joinedSlope_variation_budget L R (r / 4) (r / 2) r (2 * C / r) (C / r)
    (by linarith) (by linarith) (by positivity) (by positivity) hL hR
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hb := typeI_curvature_and_jump_budget (d * r) r (mul_pos hd0 hr0) hr0
  have he : 2 * C / r + C / r = (12 * X + 33) / r := by dsimp [C]; ring
  rw [he]
  dsimp [X] at hj ⊢
  linarith

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51AmplitudePrimitive.lean
section

namespace TaoFivePrimes

open Filter
open scoped Topology

@[fun_prop] lemma eta0_continuous : Continuous eta0 := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t < 1 / 4
  · have he : eta0 =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds ht] with u hu
      exact eta0_zero_below_quarter hu.le
    exact (continuousAt_congr he).mpr continuousAt_const
  · have ht0 : 0 < t := by linarith
    have he : eta0 =ᶠ[𝓝 t] (fun u : ℝ => 4 * max 0 (Real.log 2 - |Real.log (2 * u)|)) := by
      filter_upwards [eventually_gt_nhds ht0] with u hu
      simp [eta0, hu]
    apply (continuousAt_congr he).mpr
    fun_prop (disch := positivity)

noncomputable def typeIRealAmplitude (r d : ℝ) (c : ℂ) (y : ℝ) : ℂ :=
  ((Real.log y : ℂ) + c * (Real.log d : ℂ)) * (eta0 (y / r) : ℂ)

lemma typeI_real_amplitude_continuous (r d : ℝ) (c : ℂ) (hr : 0 < r) :
    Continuous (typeIRealAmplitude r d c) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = 0
  · subst y
    have he : typeIRealAmplitude r d c =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
      filter_upwards [eventually_lt_nhds (show (0 : ℝ) < r / 4 by positivity)] with t ht
      have hcut : eta0 (t / r) = 0 := eta0_zero_below_quarter
        ((div_le_iff₀ hr).mpr (by linarith))
      simp [typeIRealAmplitude, hcut]
    exact (continuousAt_congr he).mpr continuousAt_const
  · unfold typeIRealAmplitude
    have hcut : Continuous (fun y : ℝ => (eta0 (y / r) : ℂ)) := by fun_prop
    exact (((Real.continuousAt_log hy).ofReal).add continuousAt_const).mul hcut.continuousAt

/-- The right-hand slope agrees at all three corners with the chosen
right-continuous piecewise derivative. -/
theorem typeI_real_amplitude_right_deriv (r d y : ℝ) (c : ℂ) (hr : 0 < r) :
    HasDerivWithinAt (typeIRealAmplitude r d c) (typeIPiecewiseSlope r d c y) (Set.Ici y) y := by
  have hzero (t : ℝ) (ht : t ≤ r / 4) : typeIRealAmplitude r d c t = 0 := by
    have h := eta0_zero_below_quarter ((div_le_iff₀ hr).mpr (by linarith : t ≤ 1 / 4 * r))
    simp [typeIRealAmplitude, h]
  have hzero' (t : ℝ) (ht : r ≤ t) : typeIRealAmplitude r d c t = 0 := by
    have h := eta0_zero_above_one ((le_div_iff₀ hr).mpr (by simpa using ht))
    simp [typeIRealAmplitude, h]
  unfold typeIPiecewiseSlope joinedSlope
  split_ifs with ha hb hc
  · apply (hasDerivWithinAt_const y (Set.Ici y) (0 : ℂ)).congr_of_eventuallyEq_of_mem
    · filter_upwards [(eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht
      exact hzero t ht.le
    · exact Set.mem_Ici.mpr le_rfl
  · have hay : r / 4 ≤ y := le_of_not_gt ha
    have hy : 0 < y := lt_of_lt_of_le (by positivity) hay
    apply (log_product_hasDerivAt y hy.ne' (c * (Real.log d : ℂ)) (Real.log (4 / r))).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with t ht ht'
      change y ≤ t at ht
      exact typeI_amplitude_lower_formula r d t c hr (hy.trans_le ht)
        ((le_div_iff₀ hr).mpr (by linarith)) ((div_le_iff₀ hr).mpr (by linarith))
    · exact Set.mem_Ici.mpr le_rfl
  · have hby : r / 2 ≤ y := le_of_not_gt hb
    have hy : 0 < y := lt_of_lt_of_le (by positivity) hby
    have h := (log_product_hasDerivAt y hy.ne' (c * (Real.log d : ℂ)) (-Real.log r)).neg
    have hd : HasDerivAt
        (fun t : ℝ => -4 * ((Real.log t : ℂ) - (Real.log r : ℂ)) *
          ((Real.log t : ℂ) + c * (Real.log d : ℂ)))
        (-4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) - (Real.log r : ℂ))) y := by
      have he : (fun t : ℝ => -4 * ((Real.log t : ℂ) - (Real.log r : ℂ)) *
          ((Real.log t : ℂ) + c * (Real.log d : ℂ))) =
          -(fun t : ℝ => 4 * ((Real.log t : ℂ) + (-Real.log r : ℂ)) *
            ((Real.log t : ℂ) + c * (Real.log d : ℂ))) := by
        funext t
        simp only [Pi.neg_apply]
        ring
      rw [he]
      convert h using 1 <;> first | rfl | (push_cast; ring)
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds] with t ht ht'
      change y ≤ t at ht
      exact typeI_amplitude_upper_formula r d t c hr (hy.trans_le ht)
        ((le_div_iff₀ hr).mpr (by linarith)) ((div_le_iff₀ hr).mpr (by linarith))
    · exact Set.mem_Ici.mpr le_rfl
  · apply (hasDerivWithinAt_const y (Set.Ici y) (0 : ℂ)).congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hzero' t ((le_of_not_gt hc).trans ht)
    · exact Set.mem_Ici.mpr le_rfl

open MeasureTheory

lemma intervalIntegrable_piecewise_local (f g : ℝ → ℂ) (s : Set ℝ)
    [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (a b : ℝ)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (s.piecewise f g) volume a b :=
  ⟨Integrable.piecewise hs hf.1.integrableOn hg.1.integrableOn,
    Integrable.piecewise hs hf.2.integrableOn hg.2.integrableOn⟩

lemma typeI_slope_intervalIntegrable (r d : ℝ) (c : ℂ) (hr : 0 < r) (a b : ℝ) :
    IntervalIntegrable (typeIPiecewiseSlope r d c) volume a b := by
  let L (y : ℝ) := 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) + (Real.log (4 / r) : ℂ))
  let R (y : ℝ) := -4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) - (Real.log r : ℂ))
  have hL : ContinuousOn L (Set.Icc (r / 4) (r / 2)) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy.1
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have hyN : y ≠ 0 := hy0.ne'
    apply ContinuousAt.continuousWithinAt
    dsimp [L]
    fun_prop (disch := assumption)
  have hR : ContinuousOn R (Set.Icc (r / 2) r) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy.1
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have hyN : y ≠ 0 := hy0.ne'
    apply ContinuousAt.continuousWithinAt
    dsimp [R]
    fun_prop (disch := assumption)
  have hLc : Continuous (fun y => L (max (r / 4) (min (r / 2) y))) :=
    hL.comp_continuous (by fun_prop) (fun y => ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)
  have hRc : Continuous (fun y => R (max (r / 2) (min r y))) :=
    hR.comp_continuous (by fun_prop) (fun y => ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)
  have hstep (u : ℝ) (z : ℂ) : IntervalIntegrable (fun y => if y < u then 0 else z) volume a b :=
    intervalIntegrable_piecewise_local (fun _ => 0) (fun _ => z) (Set.Iio u)
      measurableSet_Iio a b intervalIntegrable_const intervalIntegrable_const
  have he : typeIPiecewiseSlope r d c = fun y =>
      (L (max (r / 4) (min (r / 2) y)) - L (r / 4)) +
      (R (max (r / 2) (min r y)) - R (r / 2)) +
      (if y < r / 4 then 0 else L (r / 4)) +
      (if y < r / 2 then 0 else R (r / 2) - L (r / 2)) + (if y < r then 0 else -R r) :=
    funext (fun y => joinedSlope_decomposition L R (r / 4) (r / 2) r y (by linarith) (by linarith))
  rw [he]
  exact (((((hLc.sub continuous_const).intervalIntegrable a b).add
    ((hRc.sub continuous_const).intervalIntegrable a b)).add (hstep _ _)).add (hstep _ _)).add (hstep _ _)

/-- Integral reconstruction of the literal cutoff amplitude, including corners. -/
theorem typeI_slope_integral (r d : ℝ) (c : ℂ) (hr : 0 < r) (a b : ℝ) (hab : a ≤ b) :
    (∫ y in a..b, typeIPiecewiseSlope r d c y) =
      typeIRealAmplitude r d c b - typeIRealAmplitude r d c a := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (typeI_real_amplitude_continuous r d c hr).continuousOn
  · intro y hy
    exact (typeI_real_amplitude_right_deriv r d y c hr).mono Set.Ioi_subset_Ici_self
  · exact typeI_slope_intervalIntegrable r d c hr a b

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51ConcreteDifferences.lean
section

namespace TaoFivePrimes

open MeasureTheory

theorem typeI_finite_second_difference_bound (r d a : ℝ) (c : ℂ) (N : ℕ)
    (hr : 4 ≤ r) (hd : 1 ≤ d) (hc : ‖c‖ ≤ 1) :
    (∑ n ∈ Finset.range N,
      ‖typeIRealAmplitude r d c (a + 2 * (n + 2)) -
        2 * typeIRealAmplitude r d c (a + 2 * (n + 1)) + typeIRealAmplitude r d c (a + 2 * n)‖) ≤
      96 * Real.log (4 * (d * r)) / r := by
  have hr0 : 0 < r := by linarith
  have hlog : 0 ≤ Real.log (4 * (d * r)) := Real.log_nonneg (by nlinarith)
  have h := second_difference_from_bounded_variation (typeIRealAmplitude r d c)
    (typeIPiecewiseSlope r d c) a (48 * Real.log (4 * (d * r)) / r) N (by positivity)
    (by
      intro n
      have hi := (typeI_slope_intervalIntegrable r d c hr0 (a + 2 * n) (a + 2 * n + 2)).comp_add_left (a + 2 * n)
      simpa only [sub_self, add_sub_cancel_left] using hi)
    (by
      intro n
      rw [intervalIntegral.integral_comp_add_left]
      simp only [add_zero]
      rw [typeI_slope_integral r d c hr0 _ _ (by linarith)]
      congr 1
      congr 1
      ring)
    (typeI_piecewise_slope_variation r d c hr hd hc)
  convert h using 1
  ring

/-- Passing from finite prefixes to the whole odd integer lattice. The shift
by one includes the possible first nonzero second difference at index -1. -/
theorem odd_integer_second_difference_of_prefix_bound (F : ℝ → ℂ) (B : ℝ)
    (hzero : ∀ y ≤ 1, F y = 0)
    (hprefix : ∀ N : ℕ, (∑ n ∈ Finset.range N,
      ‖F (-1 + 2 * (n + 2)) - 2 * F (-1 + 2 * (n + 1)) + F (-1 + 2 * n)‖) ≤ B) :
    (∑' n : ℤ, ‖F (2 * (n + 2) + 1) - 2 * F (2 * (n + 1) + 1) + F (2 * n + 1)‖) ≤ B := by
  let D (n : ℤ) := ‖F (2 * (n + 2) + 1) - 2 * F (2 * (n + 1) + 1) + F (2 * n + 1)‖
  let G (n : ℤ) := D (n - 1)
  have he (n : ℕ) : G n =
      ‖F (-1 + 2 * (n + 2)) - 2 * F (-1 + 2 * (n + 1)) + F (-1 + 2 * n)‖ := by
    dsimp [G, D]
    push_cast
    congr 1 <;> congr 1 <;> congr 1 <;> ring
  have hp : ∀ N : ℕ, ∑ n ∈ Finset.range N, G n ≤ B := by
    intro N
    simpa only [he] using hprefix N
  have hn (n : ℕ) : G (-(n + 1)) = 0 := by
    have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    dsimp [G, D]
    push_cast
    rw [hzero _ (by linarith), hzero _ (by linarith), hzero _ (by linarith)]
    simp
  have hs : Summable (fun n : ℕ => G n) := summable_of_sum_range_le (fun n => norm_nonneg _) hp
  have hsneg : Summable (fun n : ℕ => G (-(n + 1))) := by simp only [hn]; exact summable_zero
  have hsum := tsum_of_nat_of_neg_add_one hs hsneg
  simp only [hn, tsum_zero, add_zero] at hsum
  have hshift : (∑' n : ℤ, G n) = ∑' n : ℤ, D n := by
    exact (Equiv.addRight (-1 : ℤ)).tsum_eq D
  change (∑' n : ℤ, D n) ≤ B
  rw [← hshift, hsum]
  exact Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) hp

theorem typeI_integer_second_difference_bound (r d : ℝ) (c : ℂ)
    (hr : 4 ≤ r) (hd : 1 ≤ d) (hc : ‖c‖ ≤ 1) :
    (∑' n : ℤ, ‖typeIRealAmplitude r d c (2 * (n + 2) + 1) -
      2 * typeIRealAmplitude r d c (2 * (n + 1) + 1) + typeIRealAmplitude r d c (2 * n + 1)‖) ≤
      96 * Real.log (4 * (d * r)) / r := by
  apply odd_integer_second_difference_of_prefix_bound
  · intro y hy
    have hr0 : 0 < r := by linarith
    have hcut := eta0_zero_below_quarter ((div_le_iff₀ hr0).mpr (by linarith : y ≤ 1 / 4 * r))
    simp [typeIRealAmplitude, hcut]
  · intro N
    exact typeI_finite_second_difference_bound r d (-1) c N hr hd hc

/-- The formerly assumed concrete Type I variation estimate, now proved. -/
theorem typeI_actual_discrete_variation (x d : ℝ) (c : ℂ)
    (hd : 1 ≤ d) (hdx : 4 * d ≤ x) (hc : ‖c‖ ≤ 1) :
    (∑' n : ℤ, ‖typeIOddAmplitude x d c (n + 2) -
      2 * typeIOddAmplitude x d c (n + 1) + typeIOddAmplitude x d c n‖) ≤
      96 * Real.log (4 * x) / x * d := by
  have hd0 : 0 < d := by linarith
  have hx0 : 0 < x := by linarith
  have hr : 4 ≤ x / d := (le_div_iff₀ hd0).mpr hdx
  have h := typeI_integer_second_difference_bound (x / d) d c hr hd hc
  have he (n : ℤ) : typeIOddAmplitude x d c n = typeIRealAmplitude (x / d) d c (2 * n + 1) := by
    unfold typeIOddAmplitude typeIRealAmplitude
    push_cast
    congr 2
    field_simp
  simp_rw [he]
  have hl : d * (x / d) = x := by field_simp
  rw [hl] at h
  convert h using 1 <;> first | rfl | (push_cast; field_simp)

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51TypeIActual.lean
section

namespace TaoFivePrimes

/-- Full Type I analytic estimate for the literal odd-lattice amplitudes.
There is no Fourier-decay, smoothness, or variation hypothesis left. -/
theorem unit_typeI_actual_sum
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ)
    (hx : 1 ≤ x) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUVq : U * V < (q : ℝ) - 1) (ha : a.natAbs = 1)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ U * V ∧ d.Coprime 2)
    (hc : ∀ d ∈ s, ‖c d‖ ≤ 1)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ d ∈ s, ‖∑' n : ℤ, typeIOddAmplitude x d (c d) n *
      expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ))‖) ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
        Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  simp_rw [norm_odd_fourier_eq_geometric]
  apply unit_typeI_from_discrete_variation x alpha beta U V a q s
    (fun d => typeIOddAmplitude x d (c d)) hx hU hV hUVq ha hs hphase hbeta
  · intro d hd
    exact typeIOddAmplitude_finite x d (c d) (by linarith) (by exact_mod_cast (hs d hd).1)
  · intro d hd
    apply typeI_actual_discrete_variation x d (c d)
    · exact_mod_cast (hs d hd).1
    · have hdUV := (hs d hd).2.1
      linarith
    · exact hc d hd

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51TypeIInterface.lean
section

namespace TaoFivePrimes

/-- The complete Type I bound expressed in the public decomposition interface. -/
theorem theorem51_typeI_bound
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ) (c : ℕ → ℂ)
    (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUVq : U * V < (q : ℝ) - 1)
    (ha : a.natAbs = 1)
    (hc : ∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    theorem51TypeI x alpha U V c ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
        Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hUV : 0 ≤ U * V := mul_nonneg (by linarith) (by linarith)
  have hm := mul_nonneg (show 0 ≤ U - 40 by linarith) (show 0 ≤ V - 40 by linarith)
  have hx : 1 ≤ x := by nlinarith
  apply unit_typeI_actual_sum x alpha beta U V a q (theorem51Divisors U V) c
    hx hU hV hUVx hUVq ha _ hc hphase hbeta
  intro d hd
  obtain ⟨hd, hodd⟩ := Finset.mem_filter.mp hd
  obtain ⟨hd1, hdUV⟩ := Finset.mem_Icc.mp hd
  refine ⟨hd1, ?_, hodd⟩
  exact (Nat.cast_le.mpr hdUV).trans (Nat.floor_le hUV)

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51TypeIISpacing.lean
section

namespace TaoFivePrimes

/-- The unit numerator gives nearly 1/q spacing, stronger than 1/(2q). -/
lemma unit_half_block_window (alpha beta q j : ℝ) (hq : 4 ≤ q)
    (hj : 1 ≤ j) (hjq : j ≤ q / 2)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    (q - 1) / q ^ 2 ≤ 4 * j * alpha ∧
      4 * j * alpha ≤ 1 - (q - 1) / q ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 ≤ q - 1 := by linarith
  have hδ : 0 ≤ (q - 1) / q ^ 2 := by positivity
  have hw := unit_phase_window alpha beta q hq0 hphase hbeta
  have hlo : (q - 1) / q ^ 2 ≤ 4 * alpha := by
    have he : (q - 1) / (4 * q ^ 2) = ((q - 1) / q ^ 2) / 4 := by ring
    rw [he] at hw
    linarith [hw.1]
  have hhi : 4 * alpha ≤ (q + 1) / q ^ 2 := by
    have he : (q + 1) / (4 * q ^ 2) = ((q + 1) / q ^ 2) / 4 := by ring
    rw [he] at hw
    linarith [hw.2]
  have hα : 0 ≤ 4 * alpha := hδ.trans hlo
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hlo (by linarith : 0 ≤ j)
    have h2 := mul_le_mul_of_nonneg_right hj hδ
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hhi (by linarith : 0 ≤ j)
    have h2 := mul_le_mul_of_nonneg_right hjq (show 0 ≤ (q + 1) / q ^ 2 by positivity)
    have h3 : q / 2 * ((q + 1) / q ^ 2) ≤ 1 - (q - 1) / q ^ 2 := by
      field_simp
      nlinarith [sq_nonneg (q - 2)]
    nlinarith

lemma unit_half_block_spacing (alpha beta q j : ℝ) (hq : 4 ≤ q)
    (hj : 1 ≤ j) (hjq : j ≤ q / 2)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) (k : ℤ) :
    (q - 1) / q ^ 2 ≤ |4 * j * alpha - (k : ℝ)| := by
  have hw := unit_half_block_window alpha beta q j hq hj hjq hphase hbeta
  by_cases hk : k ≤ 0
  · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    linarith [le_abs_self (4 * j * alpha - (k : ℝ))]
  · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    linarith [neg_le_abs (4 * j * alpha - (k : ℝ))]

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51HilbertIdentity.lean
section
-- Adapted only by renaming the final theorem from accepted Prove2Me submission
-- e2c521f7-2d40-47aa-84b0-cd6cdb3872a6 (Mathlib 0df444a360eaa60ab8c11dca51a86af692955474).
-- Original: anthropics/zeta-23-lean, commit 182afbf851aa42a8ae78507be83f2356d3a33260.
-- License copy: missions/five-primes/third-party/Apache-2.0.txt.

-- from Zeta23.MV.EigenIdentity
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The Preissmann–Lévêque eigen-identity (arXiv:2203.14950 Lemma 2.1)

For real `c_r > 0`, injective real `freq`, complex `u` and real `μ` with the eigen-relation
`Σ_{n≠m} c_m c_n u_n/(freq m − freq n) = iμ u_m` for every `m`, we prove, for every `m`,

  `μ² |u_m|² = Σ_{n≠m} c_m² c_n² |u_n|²/(freq m − freq n)²
               + 2 Σ_{n≠m} c_m³ c_n Re(u_m ū_n)/(freq m − freq n)²`.

Proof (pure finite algebra): expand `|iμ u_m|²` as a double sum over `(n,p)`; the diagonal
`p = n` is the first term; off the diagonal use the partial fraction
`1/((λm−λn)(λm−λp)) = 1/((λm−λn)(λn−λp)) − 1/((λm−λp)(λn−λp))` to write the summand as
`G(n,p) + G(p,n)`, so the off-diagonal part is `2 Σ_n Σ_{p≠n,m} G(n,p)`; the inner sum is
`Re(u_n · W_n)` with `W_n = Σ_{p≠n,m} c_p ū_p/(λn−λp)`, and the conjugate eigen-relation at `n`
gives `W_n = −iμ ū_n/c_n − c_m ū_m/(λn−λm)`; the `−iμ|u_n|²/c_n` piece is purely imaginary and
dies under `Re` — the Montgomery–Vaughan cancellation — leaving the second term.
-/

noncomputable section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq : ι → ℝ}

/-- `‖z‖² = Re(z z̄)`. -/
lemma norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- `Re(u_n ū_p)` is symmetric in `(n,p)`. -/
lemma re_mul_conj_comm (a b : ℂ) : (a * conj b).re = (b * conj a).re := by
  simp [Complex.mul_re]; ring


end MV
end Zeta23

end
open Finset Complex
open scoped BigOperators ComplexConjugate
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq : ι → ℝ}

theorem TaoFivePrimes.hilbert_eigen_identity (hinj : Function.Injective freq) (c : ι → ℝ) (hc : ∀ r, 0 < c r)
    (u : ι → ℂ) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
        ((c m * c n / (freq m - freq n) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m)
    (m : ι) :
    μ ^ 2 * ‖u m‖ ^ 2 =
      (∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2)
      + 2 * ∑ n ∈ Finset.univ.erase m,
          c m ^ 3 * c n * (u m * conj (u n)).re / (freq m - freq n) ^ 2 := by
  classical
  set S : Finset ι := Finset.univ.erase m with hSdef
  have hmemS : ∀ {n : ι}, n ∈ S → n ≠ m := fun h => (Finset.mem_erase.mp h).1
  have hfr : ∀ {n p : ι}, n ≠ p → freq n - freq p ≠ 0 :=
    fun h => sub_ne_zero.mpr (fun e => h (hinj e))
  -- real coefficients a_n := c_m c_n/(λ_m − λ_n) and the real numbers R n p := Re(u_n ū_p)
  set a : ι → ℝ := fun n => c m * c n / (freq m - freq n) with hadef
  set R : ι → ι → ℝ := fun n p => (u n * conj (u p)).re with hRdef
  have hRsymm : ∀ n p, R n p = R p n := fun n p => re_mul_conj_comm _ _
  have hRdiag : ∀ n, R n n = ‖u n‖ ^ 2 := fun n => (norm_sq_eq_re_mul_conj _).symm
  /- Step A: μ²|u_m|² = Σ_n Σ_p a_n a_p R(n,p). -/
  have hA : μ ^ 2 * ‖u m‖ ^ 2 = ∑ n ∈ S, ∑ p ∈ S, a n * a p * R n p := by
    have h1 : μ ^ 2 * ‖u m‖ ^ 2 = ‖(μ : ℂ) * Complex.I * u m‖ ^ 2 := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, mul_pow,
        Real.norm_eq_abs, sq_abs]
    rw [h1, ← heig m, norm_sq_eq_re_mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    have : ((a n : ℝ) : ℂ) * u n * (((a p : ℝ) : ℂ) * conj (u p))
        = ((a n * a p : ℝ) : ℂ) * (u n * conj (u p)) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  /- Step B: split off the diagonal. -/
  have hB : ∑ n ∈ S, ∑ p ∈ S, a n * a p * R n p
      = (∑ n ∈ S, a n * a n * R n n) + ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Finset.add_sum_erase S _ hn]
  have hdiag : ∑ n ∈ S, a n * a n * R n n
      = ∑ n ∈ S, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have h1 := hfr (hmemS hn).symm
    rw [hRdiag]; simp only [hadef]; field_simp
  /- Step C: the off-diagonal part. G(n,p) := c_m² c_n c_p R(n,p)/((λm−λn)(λn−λp)). -/
  set G : ι → ι → ℝ := fun n p =>
    c m ^ 2 * c n * c p * R n p / ((freq m - freq n) * (freq n - freq p)) with hGdef
  have hF : ∀ n ∈ S, ∀ p ∈ S.erase n, a n * a p * R n p = G n p + G p n := by
    intro n hn p hp
    have hpn : p ≠ n := (Finset.mem_erase.mp hp).1
    have hpS : p ∈ S := (Finset.mem_erase.mp hp).2
    have h1 := hfr (hmemS hn).symm   -- freq m - freq n ≠ 0
    have h2 := hfr (hmemS hpS).symm  -- freq m - freq p ≠ 0
    have h3 := hfr hpn.symm          -- freq n - freq p ≠ 0
    have h4 := hfr hpn               -- freq p - freq n ≠ 0
    simp only [hadef, hGdef]
    rw [hRsymm p n]
    field_simp
    ring
  have hOff : ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p
      = 2 * ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
    have hswap : ∑ n ∈ S, ∑ p ∈ S.erase n, G p n = ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
      refine Finset.sum_comm' ?_
      intro n p
      simp only [Finset.mem_erase]
      tauto
    calc ∑ n ∈ S, ∑ p ∈ S.erase n, a n * a p * R n p
        = ∑ n ∈ S, ∑ p ∈ S.erase n, (G n p + G p n) := by
          refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun p hp => hF n hn p hp
      _ = (∑ n ∈ S, ∑ p ∈ S.erase n, G n p) + ∑ n ∈ S, ∑ p ∈ S.erase n, G p n := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => Finset.sum_add_distrib
      _ = 2 * ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by rw [hswap]; ring
  /- Step C2–C4: the inner sum, via the conjugate eigen-relation at n. -/
  have hInner : ∀ n ∈ S, ∑ p ∈ S.erase n, G n p
      = c m ^ 3 * c n * R m n / (freq m - freq n) ^ 2 := by
    intro n hn
    have hnm : n ≠ m := hmemS hn
    have h1 : freq m - freq n ≠ 0 := hfr hnm.symm
    have h1' : freq n - freq m ≠ 0 := hfr hnm
    have hcn : (c n : ℂ) ≠ 0 := by exact_mod_cast (hc n).ne'
    -- W_n := Σ_{p ∈ S.erase n} (c_p/(λn−λp)) ū_p
    set W : ℂ := ∑ p ∈ S.erase n, ((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p) with hWdef
    -- (i) Σ_p G n p = (c_m² c_n/(λm−λn)) · Re(u_n W)
    have hi : ∑ p ∈ S.erase n, G n p = c m ^ 2 * c n / (freq m - freq n) * (u n * W).re := by
      rw [hWdef, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpn : p ≠ n := (Finset.mem_erase.mp hp).1
      have h3 : freq n - freq p ≠ 0 := hfr hpn.symm
      have : u n * (((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p))
          = ((c p / (freq n - freq p) : ℝ) : ℂ) * (u n * conj (u p)) := by ring
      rw [this, Complex.re_ofReal_mul]
      simp only [hGdef, hRdef]
      field_simp
    -- (ii) the conjugate eigen-relation at n, with the p = m term split off:
    --      c_n · (c_m/(λn−λm) ū_m + W) = −iμ ū_n
    have hii : (c n : ℂ) * ((((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m) + W)
        = -((μ : ℂ) * Complex.I * conj (u n)) := by
      have hconj := congrArg conj (heig n)
      rw [map_sum] at hconj
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hconj
      -- split p = m off the sum over univ.erase n
      have hmS : m ∈ Finset.univ.erase n := Finset.mem_erase.mpr ⟨hnm.symm, Finset.mem_univ _⟩
      have hsplit := Finset.add_sum_erase (Finset.univ.erase n)
        (fun p => ((c n * c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)) hmS
      have hSS : (Finset.univ.erase n).erase m = S.erase n := by
        rw [hSdef, Finset.erase_right_comm]
      rw [hSS] at hsplit
      rw [← hsplit] at hconj
      -- factor c n out
      have hfac : ∀ p, ((c n * c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)
          = (c n : ℂ) * (((c p / (freq n - freq p) : ℝ) : ℂ) * conj (u p)) := by
        intro p; push_cast; ring
      simp only [hfac, ← Finset.mul_sum] at hconj
      rw [hWdef]
      linear_combination hconj
    -- (iii) solve for W and take Re(u_n W): the −iμ|u_n|²/c_n piece is purely imaginary
    have hiii : (u n * W).re = -(c m / (freq n - freq m)) * R n m := by
      have hW : W = -((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ)
          - (((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m) := by
        field_simp
        linear_combination hii
      have hkill : (u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))).re = 0 := by
        have hz : u n * conj (u n) = ((‖u n‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have e : u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))
            = -((μ : ℂ) / (c n : ℂ)) * (u n * conj (u n)) * Complex.I := by
          field_simp
        have : u n * (-((μ : ℂ) * Complex.I * conj (u n)) / (c n : ℂ))
            = ((-(μ / c n) * ‖u n‖ ^ 2 : ℝ) : ℂ) * Complex.I := by
          rw [e, hz]; push_cast; ring
        rw [this, Complex.re_ofReal_mul]; simp
      rw [hW, mul_sub, Complex.sub_re, hkill, zero_sub]
      have : u n * ((((c m / (freq n - freq m)) : ℝ) : ℂ) * conj (u m))
          = (((c m / (freq n - freq m)) : ℝ) : ℂ) * (u n * conj (u m)) := by ring
      rw [this, Complex.re_ofReal_mul]
      simp only [hRdef]; ring
    rw [hi, hiii, hRsymm n m]
    field_simp
    ring
  -- assemble
  rw [hA, hB, hdiag, hOff, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hInner n hn]



end


-- Source: examples/five-primes/Theorem51UniformHilbert.lean
section

namespace TaoFivePrimes

open Finset Complex
open scoped ComplexConjugate

lemma sum_offdiag_comm {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (F : ι → ι → M) :
    ∑ m, ∑ n ∈ Finset.univ.erase m, F m n = ∑ n, ∑ m ∈ Finset.univ.erase n, F m n := by
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun n => Finset.univ.erase n)]
  intro n m
  simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
  exact ⟨Ne.symm, Ne.symm⟩

/-- Uniform inverse-square row bounds give a substantially smaller Hilbert
eigenvalue constant than the nonuniform weighted estimate. -/
theorem hilbert_eigen_bound_of_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (hinj : Function.Injective freq)
    (hrow : ∀ m, ∑ n ∈ Finset.univ.erase m, 1 / (freq m - freq n) ^ 2 ≤ 4)
    (u : ι → ℂ) (hu : ∑ n, ‖u n‖ ^ 2 = 1) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
      ((1 / (freq m - freq n) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m) :
    |μ| ≤ 7 / 2 := by
  let A (m n : ι) := 1 / (freq m - freq n) ^ 2
  have hA (m n : ι) : 0 ≤ A m n := by dsimp [A]; positivity
  have hsymm (m n : ι) : A m n = A n m := by dsimp [A]; congr 1; ring
  have hR : (∑ m, ∑ n ∈ Finset.univ.erase m, A m n * ‖u m‖ ^ 2) ≤ 4 := by
    calc
      _ = ∑ m, (∑ n ∈ Finset.univ.erase m, A m n) * ‖u m‖ ^ 2 := by simp_rw [Finset.sum_mul]
      _ ≤ ∑ m, 4 * ‖u m‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_right (hrow m) (sq_nonneg _)
      _ = 4 := by rw [← Finset.mul_sum, hu]; ring
  have hS : (∑ m, ∑ n ∈ Finset.univ.erase m, A m n * ‖u n‖ ^ 2) ≤ 4 := by
    rw [sum_offdiag_comm]
    simpa only [hsymm] using hR
  have hpoint (m n : ι) : 2 * (u m * conj (u n)).re ≤ ‖u m‖ ^ 2 + ‖u n‖ ^ 2 := by
    have hh := (Complex.re_le_norm (u m * conj (u n)))
    rw [norm_mul, norm_conj] at hh
    nlinarith [sq_nonneg (‖u m‖ - ‖u n‖)]
  have hT : 2 * (∑ m, ∑ n ∈ Finset.univ.erase m, A m n * (u m * conj (u n)).re) ≤ 8 := by
    calc
      _ = ∑ m, ∑ n ∈ Finset.univ.erase m, A m n * (2 * (u m * conj (u n)).re) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ ≤ ∑ m, ∑ n ∈ Finset.univ.erase m, A m n * (‖u m‖ ^ 2 + ‖u n‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (hpoint m n) (hA m n)
      _ ≤ 8 := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        linarith
  have hid (m : ι) := hilbert_eigen_identity hinj (fun _ => 1) (fun _ => by norm_num) u μ
    (by simpa using heig) m
  simp only [one_mul, one_pow, div_eq_mul_inv] at hid
  have hsum := congrArg (fun f : ι → ℝ => ∑ m, f m) (funext hid)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hu, mul_one] at hsum
  have he : μ ^ 2 = (∑ m, ∑ n ∈ Finset.univ.erase m, A m n * ‖u n‖ ^ 2) +
      2 * (∑ m, ∑ n ∈ Finset.univ.erase m, A m n * (u m * conj (u n)).re) := by
    simpa only [A, one_div, mul_comm] using hsum
  have hμ : μ ^ 2 ≤ 12 := by linarith
  nlinarith [sq_abs μ, abs_nonneg μ]

lemma int_inverse_square_tsum_le_four : (∑' n : ℤ, 1 / (n : ℝ) ^ 2) ≤ 4 := by
  have hs : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by decide : 1 < 2)
  have he := tsum_nat_add_neg hs
  simp only [Int.cast_neg, Int.cast_natCast, Int.cast_zero, neg_sq,
    zero_pow (by decide : 2 ≠ 0), div_zero, add_zero, ← two_mul] at he
  rw [tsum_mul_left, hasSum_zeta_two.tsum_eq] at he
  rw [← he]
  have hp := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2
  nlinarith
lemma integer_inverse_square_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (m : ι) :
    (∑ n ∈ Finset.univ.erase m, 1 / ((idx m : ℝ) - (idx n : ℝ)) ^ 2) ≤ 4 := by
  let φ (n : ι) := idx m - idx n
  have hi : Function.Injective φ := by
    intro a b hab
    apply hinj
    dsimp [φ] at hab
    omega
  have hsum : (∑ n ∈ Finset.univ.erase m, 1 / ((idx m : ℝ) - (idx n : ℝ)) ^ 2) =
      ∑ k ∈ (Finset.univ.erase m).image φ, 1 / (k : ℝ) ^ 2 := by
    rw [Finset.sum_image (fun a ha b hb hab => hi hab)]
    simp only [φ, Int.cast_sub]
  rw [hsum]
  apply le_trans ((Real.summable_one_div_int_pow.mpr (by decide : 1 < 2)).sum_le_tsum
    ((Finset.univ.erase m).image φ) (fun k hk => by positivity))
  exact int_inverse_square_tsum_le_four

theorem integer_hilbert_eigen_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (u : ι → ℂ)
    (hu : ∑ n, ‖u n‖ ^ 2 = 1) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
      ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m) :
    |μ| ≤ 7 / 2 := by
  apply hilbert_eigen_bound_of_row_sum (fun n => (idx n : ℝ)) _ (integer_inverse_square_row idx hinj) u hu μ heig
  intro a b hab
  apply hinj
  change (idx a : ℝ) = (idx b : ℝ) at hab
  exact_mod_cast hab

end TaoFivePrimes


end


-- Source: examples/five-primes/Theorem51SpectralBound.lean
section

namespace TaoFivePrimes
open Matrix Finset
open scoped ComplexConjugate

/-- Spectral expansion of a finite Hermitian quadratic form.
Adapted from the Apache-2.0 Zeta23.MV spectral expansion (Anthropic, 2026),
using Mathlib's spectral theorem directly. -/
theorem hermitian_quadratic_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    star x ⬝ᵥ (A *ᵥ x) =
      ((∑ i, hA.eigenvalues i *
        ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) U, hsc, ← hc_def]
  simp only [Function.comp_apply, dotProduct, mulVec_diagonal, Pi.star_apply,
    Complex.star_def, RCLike.ofReal_eq_complex_ofReal]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.conj_mul', mul_left_comm]

/-- A unitary change of coordinates preserves the sum of squared moduli. -/
theorem unitary_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (x : ι → ℂ) :
    ∑ i, ‖(star (U : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  have he : star (star (U : Matrix ι ι ℂ) *ᵥ x) ⬝ᵥ
      (star (U : Matrix ι ι ℂ) *ᵥ x) = star x ⬝ᵥ x := by
    rw [star_mulVec, show (star (U : Matrix ι ι ℂ))ᴴ = U from
      conjTranspose_conjTranspose (U : Matrix ι ι ℂ), ← dotProduct_mulVec,
      mulVec_mulVec, ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mulVec]
  have hn (v : ι → ℂ) : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def,
      Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]
  rw [hn, hn] at he
  exact_mod_cast he

theorem hermitian_quadratic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (B : ℝ)
    (hB : ∀ i, |hA.eigenvalues i| ≤ B) (x : ι → ℂ) :
    ‖star x ⬝ᵥ (A *ᵥ x)‖ ≤ B * ∑ i, ‖x i‖ ^ 2 := by
  rw [hermitian_quadratic_expansion hA x, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ∑ i, |hA.eigenvalues i *
        ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, B * ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow, abs_norm]
      exact mul_le_mul_of_nonneg_right (hB i) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, unitary_energy]

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51IntegerHilbertForm.lean
section

namespace TaoFivePrimes
open Matrix Finset
open scoped ComplexConjugate

noncomputable def integerHilbertMatrix {ι : Type*} (idx : ι → ℤ) : Matrix ι ι ℂ :=
  fun m n => Complex.I * ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ)

lemma integerHilbertMatrix_hermitian {ι : Type*} (idx : ι → ℤ) :
    (integerHilbertMatrix idx).IsHermitian := by
  ext m n
  simp only [integerHilbertMatrix, conjTranspose_apply, map_mul, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal]
  rw [show (idx n : ℝ) - idx m = -((idx m : ℝ) - idx n) by ring]
  push_cast
  simp only [one_div, inv_neg, neg_mul, mul_neg, neg_neg]

theorem integerHilbertMatrix_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (j : ι) :
    |(integerHilbertMatrix_hermitian idx).eigenvalues j| ≤ 7 / 2 := by
  let hA := integerHilbertMatrix_hermitian idx
  let u := hA.eigenvectorBasis j
  have hu : ∑ n, ‖u n‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq]
    have hh := hA.eigenvectorBasis.orthonormal.1 j
    change ‖u‖ = 1 at hh
    rw [hh, one_pow]
  have he (m : ι) : ∑ n ∈ univ.erase m,
      ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * u n =
        ((-hA.eigenvalues j : ℝ) : ℂ) * Complex.I * u m := by
    have hh := congrFun (hA.mulVec_eigenvectorBasis j) m
    change (∑ n, Complex.I * ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * u n) =
      (hA.eigenvalues j : ℂ) * u m at hh
    have hs : (∑ n, ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * u n) =
        ∑ n ∈ univ.erase m, ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * u n := by
      rw [← sum_erase_add _ _ (mem_univ m)]
      simp
    simp_rw [mul_assoc] at hh
    rw [← mul_sum, hs] at hh
    have hmul := congrArg (fun z : ℂ => -Complex.I * z) hh
    simp only [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul] at hmul
    rw [hmul, Complex.ofReal_neg]
    ring
  have hb := integer_hilbert_eigen_bound idx hinj (fun n => u n) hu
    (-hA.eigenvalues j) he
  simpa only [abs_neg] using hb

theorem integer_hilbert_quadratic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (x : ι → ℂ) :
    ‖star x ⬝ᵥ (integerHilbertMatrix idx *ᵥ x)‖ ≤ (7 / 2 : ℝ) * ∑ i, ‖x i‖ ^ 2 :=
  hermitian_quadratic_bound (integerHilbertMatrix_hermitian idx) (7 / 2)
    (integerHilbertMatrix_eigenvalues idx hinj) x

/-- The integer Hilbert inequality in the double-sum form needed by the sine kernel. -/
theorem integer_hilbert_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (x : ι → ℂ) :
    ‖∑ m, ∑ n ∈ univ.erase m,
      star (x m) * ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * x n‖ ≤
        (7 / 2 : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
  have he : star x ⬝ᵥ (integerHilbertMatrix idx *ᵥ x) = Complex.I *
      (∑ m, ∑ n ∈ univ.erase m,
        star (x m) * ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * x n) := by
    simp only [dotProduct, mulVec, integerHilbertMatrix, Pi.star_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← sum_erase_add _ _ (mem_univ m)]
    simp only [sub_self, div_zero, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hb := integer_hilbert_quadratic_bound idx hinj x
  rw [he, norm_mul, Complex.norm_I, one_mul] at hb
  exact hb

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51KernelError.lean
section

namespace TaoFivePrimes
open Finset

/-- A bounded off-diagonal kernel costs at most one unit per other index. -/
theorem bounded_kernel_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → ℂ) (hE : ∀ m n, m ≠ n → ‖E m n‖ ≤ 1) (x : ι → ℂ) :
    ‖∑ m, ∑ n ∈ univ.erase m, star (x m) * E m n * x n‖ ≤
      ((Fintype.card ι : ℝ) - 1) * ∑ m, ‖x m‖ ^ 2 := by
  have hp (m n : ι) (hn : n ∈ univ.erase m) :
      ‖star (x m) * E m n * x n‖ ≤ (‖x m‖ ^ 2 + ‖x n‖ ^ 2) / 2 := by
    rw [norm_mul, norm_mul, norm_star]
    have he := hE m n (Ne.symm (mem_erase.mp hn).1)
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (norm_nonneg (x m))) (norm_nonneg (x n))
    nlinarith [sq_nonneg (‖x m‖ - ‖x n‖)]
  have hcard (m : ι) : ((univ.erase m).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    have hh := Finset.card_erase_add_one (s := (univ : Finset ι)) (mem_univ m)
    have hh' : ((univ.erase m).card : ℝ) + 1 = (Fintype.card ι : ℝ) := by
      exact_mod_cast hh
    linarith
  have hs : (∑ m, ∑ n ∈ univ.erase m, ‖x n‖ ^ 2) =
      ((Fintype.card ι : ℝ) - 1) * ∑ m, ‖x m‖ ^ 2 := by
    rw [Finset.sum_comm' (t' := univ) (s' := fun n => univ.erase n)]
    · simp only [sum_const, nsmul_eq_mul, hcard, ← mul_sum]
    · intro n m
      simp only [mem_univ, mem_erase, true_and, and_true]
      exact ⟨Ne.symm, Ne.symm⟩
  calc
    _ ≤ ∑ m, ∑ n ∈ univ.erase m, ‖star (x m) * E m n * x n‖ := by
      exact (norm_sum_le _ _).trans (sum_le_sum fun m hm => norm_sum_le _ _)
    _ ≤ ∑ m, ∑ n ∈ univ.erase m, (‖x m‖ ^ 2 + ‖x n‖ ^ 2) / 2 := by
      exact sum_le_sum fun m hm => sum_le_sum fun n hn => hp m n hn
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib, sum_const, nsmul_eq_mul]
      rw [hs]
      simp only [hcard, ← mul_sum]
      ring

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51CosecantError.lean
section

namespace TaoFivePrimes

/-- A coarse but sufficient Hilbert-kernel approximation on a half-circle. -/
lemma cosecant_sub_inv_le_one (t : ℝ) (ht : 0 < t) (hmax : t ≤ 8 / 5) :
    |1 / Real.sin t - 1 / t| ≤ 1 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_gt_three])
  have hsle : Real.sin t ≤ t := Real.sin_le ht.le
  have hnonneg : 0 ≤ 1 / Real.sin t - 1 / t := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le hs hsle
  rw [abs_of_nonneg hnonneg]
  have hsq : t ^ 2 ≤ (8 / 5 : ℝ) ^ 2 := (sq_le_sq₀ ht.le (by norm_num)).mpr hmax
  have hpoly : 0 ≤ 6 - t - t ^ 2 := by nlinarith
  have hmul : 0 ≤ t ^ 2 * (6 - t - t ^ 2) := mul_nonneg (sq_nonneg _) hpoly
  have hsin := Real.sin_ge_sub_cube ht.le
  have hprod := mul_le_mul_of_nonneg_right hsin (show 0 ≤ 1 + t by linarith)
  have hmain : t ≤ (1 + t) * Real.sin t := by nlinarith
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hs).mpr
  rw [show (1 + 1 / t) * Real.sin t = ((1 + t) * Real.sin t) / t by field_simp; ring]
  exact (le_div_iff₀ ht).mpr (by simpa using hmain)

lemma abs_cosecant_sub_inv_le_one (t : ℝ) (ht : t ≠ 0) (hmax : |t| ≤ 8 / 5) :
    |1 / Real.sin t - 1 / t| ≤ 1 := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have h := cosecant_sub_inv_le_one (-t) (by linarith) (by simpa [abs_of_neg ht] using hmax)
    simpa only [Real.sin_neg, div_neg, neg_sub_neg, abs_sub_comm] using h
  · exact cosecant_sub_inv_le_one t ht (by simpa [abs_of_pos ht] using hmax)

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51KernelConstants.lean
section

namespace TaoFivePrimes

/-- The coarse integer Hilbert bound still fits the required 2q budget. -/
theorem unit_kernel_constant (q h : ℝ) (hq : 40 ≤ q)
    (hh : (q - 1) / q ^ 2 ≤ h) :
    1 + (7 / 2 : ℝ) / (Real.pi * h) + q / 2 ≤ 2 * q := by
  have hq0 : 0 < q := by linarith
  have hδ : 0 < (q - 1) / q ^ 2 := div_pos (by linarith) (sq_pos_of_pos hq0)
  have hh0 : 0 < h := hδ.trans_le hh
  have hp : 0 < Real.pi * h := mul_pos Real.pi_pos hh0
  have hh' : q - 1 ≤ h * q ^ 2 := (div_le_iff₀ (sq_pos_of_pos hq0)).mp hh
  have hc : 0 ≤ 3 * q / 2 - 1 := by linarith
  have hmain : (7 / 2 : ℝ) ≤ (3 * q / 2 - 1) * (Real.pi * h) := by
    have ha := mul_le_mul_of_nonneg_left hh' (show 0 ≤ 3 * (3 * q / 2 - 1) by positivity)
    have hb := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
      (mul_nonneg hc hh0.le)
    have hpoly := mul_nonneg hq0.le (show 0 ≤ q - 8 by linarith)
    have ht : (7 / 2 : ℝ) * q ^ 2 ≤ ((3 * q / 2 - 1) * (3 * h)) * q ^ 2 := by
      nlinarith
    have ht' : (7 / 2 : ℝ) ≤ (3 * q / 2 - 1) * (3 * h) :=
      (mul_le_mul_iff_left₀ (sq_pos_of_pos hq0)).mp (by nlinarith [ht])
    nlinarith
  have hf := (div_le_iff₀ hp).mpr hmain
  linarith

/-- A half-modulus block lies inside the interval where the cosecant error
is at most one. -/
theorem unit_kernel_angle (q h t : ℝ) (hq : 100 ≤ q) (hh0 : 0 ≤ h)
    (hh : h ≤ (q + 1) / q ^ 2) (ht : |t| ≤ q / 2) :
    |(Real.pi * h) * t| ≤ 8 / 5 := by
  have hq0 : 0 < q := by linarith
  have h1 : h * q ≤ (q + 1) / q := by
    have hb := (le_div_iff₀ (sq_pos_of_pos hq0)).mp hh
    apply (le_div_iff₀ hq0).mpr
    nlinarith [hb]
  have h2 : h * q ≤ (101 / 100 : ℝ) := by
    have hb : (q + 1) / q ≤ (101 / 100 : ℝ) := by
      apply (div_le_iff₀ hq0).mpr
      linarith
    exact h1.trans hb
  rw [abs_mul, abs_of_nonneg (mul_nonneg Real.pi_pos.le hh0)]
  have ha := mul_le_mul_of_nonneg_left ht (mul_nonneg Real.pi_pos.le hh0)
  have hb := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
  have hc := Real.pi_lt_d2
  nlinarith

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51CosecantForm.lean
section

namespace TaoFivePrimes
open Finset

/-- Integer-grid cosecant quadratic form on a short arc. -/
theorem cosecant_quadratic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (k : ℝ) (hk : 0 < k)
    (hwidth : ∀ m n, |k * ((idx m : ℝ) - (idx n : ℝ))| ≤ 8 / 5)
    (x : ι → ℂ) :
    ‖∑ m, ∑ n ∈ univ.erase m, star (x m) *
      ((1 / Real.sin (k * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * x n‖ ≤
      ((7 / 2 : ℝ) / k + ((Fintype.card ι : ℝ) - 1)) * ∑ m, ‖x m‖ ^ 2 := by
  let E (m n : ι) : ℂ := ((1 / Real.sin (k * ((idx m : ℝ) - (idx n : ℝ))) -
    1 / (k * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ)
  have hE (m n : ι) (hmn : m ≠ n) : ‖E m n‖ ≤ 1 := by
    have hd : (idx m : ℝ) - (idx n : ℝ) ≠ 0 := by
      intro he
      apply hmn
      apply hinj
      exact_mod_cast (sub_eq_zero.mp he)
    simpa only [E, Complex.norm_real, Real.norm_eq_abs] using
      abs_cosecant_sub_inv_le_one _ (mul_ne_zero hk.ne' hd) (hwidth m n)
  have hsplit : (∑ m, ∑ n ∈ univ.erase m, star (x m) *
      ((1 / Real.sin (k * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * x n) =
      ((1 / k : ℝ) : ℂ) * (∑ m, ∑ n ∈ univ.erase m, star (x m) *
        ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * x n) +
      (∑ m, ∑ n ∈ univ.erase m, star (x m) * E m n * x n) := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    dsimp [E]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hsplit]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hk)]
  calc
    _ ≤ (1 / k) * ((7 / 2 : ℝ) * ∑ m, ‖x m‖ ^ 2) +
        ((Fintype.card ι : ℝ) - 1) * ∑ m, ‖x m‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left (integer_hilbert_sum_bound idx hinj x)
        (by positivity)) (bounded_kernel_error E hE x)
    _ = _ := by ring

/-- The sine-kernel bound in the unit-numerator half-block regime, with
the precise budget required for the subsequent exponential Gram estimate. -/
theorem unit_cosecant_block_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (hcard : (Fintype.card ι : ℝ) - 1 ≤ q / 2) (x : ι → ℂ) :
    ‖∑ m, ∑ n ∈ univ.erase m, star (x m) *
      ((1 / Real.sin ((Real.pi * h) * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * x n‖ ≤
      (2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
  have hh : 0 < h := lt_of_lt_of_le (div_pos (by linarith) (by positivity)) hlo
  have hb := cosecant_quadratic_bound idx hinj (Real.pi * h) (mul_pos Real.pi_pos hh)
    (fun m n => unit_kernel_angle q h _ hq hh.le hhi (hwidth m n)) x
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun m hm => sq_nonneg _)
  have hc := unit_kernel_constant q h (by linarith) hlo
  linarith

/-- The difference of two phase-conjugated cosecant forms retains the same
bound after division by 2i. This is the off-diagonal geometric-sum pattern. -/
theorem unit_cosecant_phase_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (hcard : (Fintype.card ι : ℝ) - 1 ≤ q / 2)
    (p r x : ι → ℂ) (hp : ∀ j, ‖p j‖ = 1) (hr : ∀ j, ‖r j‖ = 1) :
    ‖∑ m, ∑ n ∈ univ.erase m, star (x m) *
      ((star (p m) * p n - star (r m) * r n) / (2 * Complex.I)) *
      ((1 / Real.sin ((Real.pi * h) * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * x n‖ ≤
      (2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
  let Q (v : ι → ℂ) : ℂ := ∑ m, ∑ n ∈ univ.erase m, star (v m * x m) *
    ((1 / Real.sin ((Real.pi * h) * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * (v n * x n)
  have hQ (v : ι → ℂ) (hv : ∀ j, ‖v j‖ = 1) :
      ‖Q v‖ ≤ (2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
    have hb := unit_cosecant_block_bound idx hinj q h hq hlo hhi hwidth hcard
      (fun j => v j * x j)
    simpa only [Q, norm_mul, hv, one_mul] using hb
  have he : (∑ m, ∑ n ∈ univ.erase m, star (x m) *
      ((star (p m) * p n - star (r m) * r n) / (2 * Complex.I)) *
      ((1 / Real.sin ((Real.pi * h) * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * x n) =
      (Q p - Q r) / (2 * Complex.I) := by
    dsimp [Q]
    simp only [sum_div, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    simp only [map_mul]
    ring
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [he, norm_div, norm_mul, Complex.norm_I, htwo, mul_one]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have hb := (norm_sub_le (Q p) (Q r)).trans (add_le_add (hQ p hp) (hQ r hr))
  nlinarith

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51GeometricKernel.lean
section

namespace TaoFivePrimes
open Finset

/-- The angular additive character used in the finite Gram calculation. -/
noncomputable def angularPhase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

lemma angularPhase_add (s t : ℝ) :
    angularPhase (s + t) = angularPhase s * angularPhase t := by
  simp only [angularPhase, Complex.ofReal_add, add_mul, Complex.exp_add]

lemma angularPhase_norm (t : ℝ) : ‖angularPhase t‖ = 1 := by
  simp [angularPhase, Complex.norm_exp]

lemma angularPhase_sine (t : ℝ) :
    2 * Complex.I * (Real.sin t : ℂ) = angularPhase t - angularPhase (-t) := by
  unfold angularPhase
  rw [Complex.exp_ofReal_mul_I t, Complex.exp_ofReal_mul_I (-t)]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

/-- Finite geometric-sum identity without a division or nonvanishing assumption. -/
theorem angular_geometric_kernel (t : ℝ) (N : ℕ) :
    (2 * Complex.I * (Real.sin t : ℂ)) *
      (∑ j ∈ range N, angularPhase (2 * (j : ℝ) * t)) =
      angularPhase ((2 * (N : ℝ) - 1) * t) - angularPhase (-t) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih]
    have hplus : angularPhase ((2 * ((N + 1 : ℕ) : ℝ) - 1) * t) =
        angularPhase (2 * (N : ℝ) * t) * angularPhase t := by
      rw [← angularPhase_add]
      congr 1
      push_cast
      ring
    have hminus : angularPhase ((2 * (N : ℝ) - 1) * t) =
        angularPhase (2 * (N : ℝ) * t) * angularPhase (-t) := by
      rw [← angularPhase_add]
      congr 1
      ring
    rw [hplus, hminus, angularPhase_sine]
    ring

theorem angular_geometric_cosecant (t : ℝ) (N : ℕ) (ht : Real.sin t ≠ 0) :
    (∑ j ∈ range N, angularPhase (2 * (j : ℝ) * t)) =
      (angularPhase ((2 * (N : ℝ) - 1) * t) - angularPhase (-t)) /
        (2 * Complex.I) * ((1 / Real.sin t : ℝ) : ℂ) := by
  have hs : (Real.sin t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hi := angular_geometric_kernel t N
  rw [Complex.ofReal_div, Complex.ofReal_one, ← hi]
  field_simp
  apply sum_congr rfl
  intro j hj
  congr 1
  ring

lemma angularPhase_star (t : ℝ) : star (angularPhase t) = angularPhase (-t) := by
  simp only [angularPhase, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  congr 1
  ring

lemma angularPhase_star_mul (c u v : ℝ) :
    star (angularPhase (c * u)) * angularPhase (c * v) =
      angularPhase (c * (v - u)) := by
  rw [angularPhase_star, ← angularPhase_add]
  congr 1
  ring

lemma angularPhase_zero : angularPhase 0 = 1 := by simp [angularPhase]

/-- Pure finite algebra for the Gram matrix of a family of coefficient rows. -/
theorem finite_gram_expansion {ι J : Type*} [Fintype ι]
    (s : Finset J) (A : J → ι → ℂ) (x : ι → ℂ) :
    ((∑ j ∈ s, ‖∑ m, A j m * x m‖ ^ 2 : ℝ) : ℂ) =
      ∑ m, ∑ n, star (x m) * (∑ j ∈ s, star (A j m) * A j n) * x n := by
  have hn (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
    rw [Complex.star_def, Complex.conj_mul']
    exact Complex.ofReal_pow _ _
  rw [Complex.ofReal_sum]
  simp only [hn, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro j hj
  ring

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51FiniteLargeSieve.lean
section

namespace TaoFivePrimes
open Finset

lemma sin_ne_zero_short_arc (t : ℝ) (ht : t ≠ 0) (hb : |t| ≤ 8 / 5) :
    Real.sin t ≠ 0 := by
  rcases lt_or_gt_of_ne ht with h | h
  · have hs := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr h)
      (show -t < Real.pi by linarith [neg_le_abs t, Real.pi_gt_three])
    rw [Real.sin_neg] at hs
    linarith
  · exact (Real.sin_pos_of_pos_of_lt_pi h
      (by linarith [le_abs_self t, Real.pi_gt_three])).ne'

/-- Off-diagonal geometric kernel represented by two unit phases. -/
lemma angular_kernel_two_phases (k u v : ℝ) (N : ℕ)
    (ht : Real.sin (k * (u - v)) ≠ 0) :
    (∑ j ∈ range N, star (angularPhase ((-2 * (j : ℝ) * k) * u)) *
      angularPhase ((-2 * (j : ℝ) * k) * v)) =
    ((star (angularPhase ((-(2 * (N : ℝ) - 1) * k) * u)) *
        angularPhase ((-(2 * (N : ℝ) - 1) * k) * v) -
      star (angularPhase (k * u)) * angularPhase (k * v)) / (2 * Complex.I)) *
      ((1 / Real.sin (k * (u - v)) : ℝ) : ℂ) := by
  simp only [angularPhase_star_mul]
  have harg (j : ℕ) : -2 * (j : ℝ) * k * (v - u) =
      2 * (j : ℝ) * (k * (u - v)) := by ring
  simp only [harg]
  rw [angular_geometric_cosecant _ N ht]
  congr 3 <;> congr 1 <;> ring

/-- Finite large-sieve estimate on a half-modulus integer block.
The conclusion concerns the actual exponential sums, not an assumed kernel bound. -/
theorem unit_finite_large_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (hcard : (Fintype.card ι : ℝ) - 1 ≤ q / 2) (N : ℕ) (x : ι → ℂ) :
    (∑ j ∈ range N, ‖∑ m, angularPhase ((-2 * (j : ℝ) * (Real.pi * h)) * idx m) * x m‖ ^ 2) ≤
      ((N : ℝ) + 2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
  let k := Real.pi * h
  let A (j : ℕ) (m : ι) := angularPhase ((-2 * (j : ℝ) * k) * idx m)
  let K (m n : ι) := ∑ j ∈ range N, star (A j m) * A j n
  let O : ℂ := ∑ m, ∑ n ∈ univ.erase m, star (x m) * K m n * x n
  have hh : 0 < h := lt_of_lt_of_le (div_pos (by linarith) (by positivity)) hlo
  have hkn (m n : ι) (hmn : n ≠ m) : Real.sin (k * ((idx m : ℝ) - (idx n : ℝ))) ≠ 0 := by
    apply sin_ne_zero_short_arc
    · apply mul_ne_zero (mul_pos Real.pi_pos hh).ne'
      intro he
      apply hmn
      apply hinj
      exact_mod_cast (sub_eq_zero.mp he).symm
    · exact unit_kernel_angle q h _ hq hh.le hhi (hwidth m n)
  have hO : ‖O‖ ≤ (2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
    have hb := unit_cosecant_phase_difference idx hinj q h hq hlo hhi hwidth hcard
      (fun m => angularPhase ((-(2 * (N : ℝ) - 1) * k) * idx m))
      (fun m => angularPhase (k * idx m)) x
      (fun m => angularPhase_norm _) (fun m => angularPhase_norm _)
    convert hb using 1
    congr 1
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    dsimp [K, A]
    have he := angular_kernel_two_phases k (idx m) (idx n) N (hkn m n (mem_erase.mp hn).1)
    simp only [Complex.star_def] at he
    rw [he]
    ring
  have hdiag (m : ι) : K m m = (N : ℂ) := by
    simp only [K, A, angularPhase_star_mul, sub_self, mul_zero, angularPhase_zero,
      sum_const, card_range, nsmul_eq_mul, mul_one]
  have hgram := finite_gram_expansion (range N) A x
  have hsplit : (∑ m, ∑ n, star (x m) * K m n * x n) =
      (((N : ℝ) * ∑ m, ‖x m‖ ^ 2 : ℝ) : ℂ) + O := by
    have hs (m : ι) : (∑ n, star (x m) * K m n * x n) =
        (N : ℂ) * (star (x m) * x m) +
        ∑ n ∈ univ.erase m, star (x m) * K m n * x n := by
      rw [← sum_erase_add _ _ (mem_univ m), hdiag]
      ring
    simp only [Complex.star_def] at hs ⊢
    simp only [hs, sum_add_distrib, ← mul_sum, Complex.conj_mul']
    simp only [O, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.star_def]
  change _ = ∑ m, ∑ n, star (x m) * K m n * x n at hgram
  rw [hsplit] at hgram
  have hn := congrArg norm hgram
  have hnonneg : 0 ≤ ∑ j ∈ range N, ‖∑ m, A j m * x m‖ ^ 2 := sum_nonneg fun j hj => sq_nonneg _
  have henergy : 0 ≤ (N : ℝ) * ∑ m, ‖x m‖ ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun m hm => sq_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hn
  have hb := (norm_add_le (((N : ℝ) * ∑ m, ‖x m‖ ^ 2 : ℝ) : ℂ) O).trans
    (add_le_add le_rfl hO)
  rw [← hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg henergy] at hb
  dsimp [A, k] at hb
  nlinarith

/-- Translating the row interval only rotates each coefficient by a unit phase. -/
theorem unit_finite_large_sieve_translate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (hcard : (Fintype.card ι : ℝ) - 1 ≤ q / 2) (N : ℕ) (t : ℝ) (x : ι → ℂ) :
    (∑ j ∈ range N, ‖∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * x m‖ ^ 2) ≤
      ((N : ℝ) + 2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
  have hb := unit_finite_large_sieve idx hinj q h hq hlo hhi hwidth hcard N
    (fun m => angularPhase ((-2 * t * (Real.pi * h)) * idx m) * x m)
  simp only [norm_mul, angularPhase_norm, one_mul] at hb
  convert hb using 1
  apply sum_congr rfl
  intro j hj
  congr 2
  apply sum_congr rfl
  intro m hm
  have he : angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) =
      angularPhase ((-2 * (j : ℝ) * (Real.pi * h)) * idx m) *
        angularPhase ((-2 * t * (Real.pi * h)) * idx m) := by
    rw [← angularPhase_add]
    congr 1
    ring
  rw [he]
  ring

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51BlockCounting.lean
section

namespace TaoFivePrimes
open Finset

/-- An integer set of diameter at most L contains at most L+1 points. -/
theorem integer_set_card_le (s : Finset ℤ) (L : ℝ) (hL : 0 ≤ L)
    (hdiam : ∀ a ∈ s, ∀ b ∈ s, |(a : ℝ) - (b : ℝ)| ≤ L) :
    (s.card : ℝ) - 1 ≤ L := by
  by_cases hs : s.Nonempty
  · have hmin := s.min'_mem hs
    have hmax := s.max'_mem hs
    have horder : s.min' hs ≤ s.max' hs := s.min'_le _ hmax
    have hsub : s ⊆ Icc (s.min' hs) (s.max' hs) := by
      intro a ha
      exact mem_Icc.mpr ⟨s.min'_le a ha, s.le_max' a ha⟩
    have hc := card_le_card hsub
    have hi := Int.card_Icc_of_le (s.min' hs) (s.max' hs) (show s.min' hs ≤ s.max' hs + 1 by omega)
    have hiR : ((Icc (s.min' hs) (s.max' hs)).card : ℝ) =
        (s.max' hs : ℝ) + 1 - (s.min' hs : ℝ) := by exact_mod_cast hi
    have hcR : (s.card : ℝ) ≤ ((Icc (s.min' hs) (s.max' hs)).card : ℝ) := by exact_mod_cast hc
    have hd := hdiam _ hmax _ hmin
    rw [hiR] at hcR
    linarith [le_abs_self ((s.max' hs : ℝ) - (s.min' hs : ℝ))]
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp only [he, card_empty, Nat.cast_zero, zero_sub]
    linarith

theorem integer_index_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (L : ℝ) (hL : 0 ≤ L)
    (hdiam : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ L) :
    (Fintype.card ι : ℝ) - 1 ≤ L := by
  have hc := integer_set_card_le (univ.image idx) L hL (by
    intro a ha b hb
    obtain ⟨m, hm, rfl⟩ := mem_image.mp ha
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hb
    exact hdiam m n)
  simpa only [card_image_of_injective _ hinj, card_univ] using hc

/-- Odd integers in a real interval have density at most one half, with
one endpoint allowance. This retains the constants in Type II counting. -/
theorem odd_integer_interval_card (s : Finset ℤ) (A B : ℝ) (hAB : A ≤ B)
    (hs : ∀ n ∈ s, A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B ∧ n % 2 = 1) :
    (s.card : ℝ) ≤ (B - A) / 2 + 1 := by
  have hid (n : ℤ) (hn : n ∈ s) : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) + 1 := by
    have hm := (hs n hn).2.2
    have he : n = 2 * (n / 2) + 1 := by omega
    exact_mod_cast he
  have hi : Set.InjOn (fun n : ℤ => n / 2) (s : Set ℤ) := by
    intro m hm n hn he
    change m / 2 = n / 2 at he
    have hm' := (hs m hm).2.2
    have hn' := (hs n hn).2.2
    omega
  have hc := integer_set_card_le (s.image (fun n => n / 2)) ((B - A) / 2)
    (by linarith) (by
      intro a ha b hb
      obtain ⟨m, hm, rfl⟩ := mem_image.mp ha
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hb
      have hm' := hs m hm
      have hn' := hs n hn
      have em := hid m hm
      have en := hid n hn
      rw [abs_le]
      constructor <;> linarith)
  rw [Finset.card_image_iff.mpr hi] at hc
  linarith

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51BilinearBlock.lean
section

namespace TaoFivePrimes
open Finset

/-- Bilinear half-block bound with no separate cardinality hypothesis. -/
theorem unit_bilinear_block_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (N : ℕ) (t : ℝ) (a : ℕ → ℂ) (x : ι → ℂ) :
    ‖∑ j ∈ range N, a j *
      (∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * x m)‖ ^ 2 ≤
      ((N : ℝ) + 2 * q - 1) * (∑ m, ‖x m‖ ^ 2) * ∑ j ∈ range N, ‖a j‖ ^ 2 := by
  let F (j : ℕ) := ∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * x m
  have hcard := integer_index_card_le idx hinj (q / 2) (by linarith) hwidth
  have hLS := unit_finite_large_sieve_translate idx hinj q h hq hlo hhi hwidth hcard N t x
  have hn : ‖∑ j ∈ range N, a j * F j‖ ≤ ∑ j ∈ range N, ‖a j‖ * ‖F j‖ := by
    simpa only [norm_mul] using norm_sum_le (range N) (fun j => a j * F j)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (sum_nonneg fun j hj =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  have hCS := sum_mul_sq_le_sq_mul_sq (range N) (fun j => ‖a j‖) (fun j => ‖F j‖)
  have hmul := mul_le_mul_of_nonneg_left hLS
    (show 0 ≤ ∑ j ∈ range N, ‖a j‖ ^ 2 from sum_nonneg fun j hj => sq_nonneg _)
  change ‖∑ j ∈ range N, a j * F j‖ ^ 2 ≤ _
  exact (hsq.trans hCS).trans (by simpa only [F, mul_comm, mul_left_comm, mul_assoc] using hmul)

theorem unit_bilinear_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (N : ℕ) (t : ℝ) (a : ℕ → ℂ) (x : ι → ℂ) :
    ‖∑ j ∈ range N, a j *
      (∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * x m)‖ ≤
      Real.sqrt (((N : ℝ) + 2 * q - 1) * (∑ m, ‖x m‖ ^ 2) * ∑ j ∈ range N, ‖a j‖ ^ 2) :=
  Real.le_sqrt_of_sq_le (unit_bilinear_block_sq idx hinj q h hq hlo hhi hwidth N t a x)

/-- Cauchy--Schwarz across blocks, retaining the number of blocks exactly. -/
lemma complex_sum_sq_le_card_energy {B : Type*} (s : Finset B) (F : B → ℂ) :
    ‖∑ b ∈ s, F b‖ ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, ‖F b‖ ^ 2 := by
  have ht := norm_sum_le s F
  have hs := (sq_le_sq₀ (norm_nonneg _) (sum_nonneg fun b hb => norm_nonneg _)).mpr ht
  have hc := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun b => ‖F b‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hc
  exact hs.trans hc

/-- Subdivision into integer half-blocks, before specializing the partition. -/
theorem unit_bilinear_blocks {B ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset B) (idx : B → ι → ℤ) (hinj : ∀ b, Function.Injective (idx b))
    (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ b m n, |(idx b m : ℝ) - (idx b n : ℝ)| ≤ q / 2)
    (N : ℕ) (t : ℝ) (a : ℕ → ℂ) (x : B → ι → ℂ) :
    ‖∑ b ∈ s, ∑ j ∈ range N, a j *
      (∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx b m) * x b m)‖ ≤
      Real.sqrt ((s.card : ℝ) * ((N : ℝ) + 2 * q - 1) *
        (∑ b ∈ s, ∑ m, ‖x b m‖ ^ 2) * ∑ j ∈ range N, ‖a j‖ ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  apply (complex_sum_sq_le_card_energy s _).trans
  have hb := sum_le_sum (s := s) (fun b hb =>
    unit_bilinear_block_sq (idx b) (hinj b) q h hq hlo hhi (hwidth b) N t a (x b))
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg s.card : (0 : ℝ) ≤ s.card)
  simpa only [← sum_mul, ← mul_sum, mul_assoc] using hm

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51TypeIICounts.lean
section

namespace TaoFivePrimes

theorem odd_row_count (s : Finset ℤ) (W : ℝ) (hW : 40 ≤ W)
    (hs : ∀ w ∈ s, W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W ∧ w % 2 = 1) :
    (s.card : ℝ) ≤ 1.1 * W / 4 := by
  have hc := odd_integer_interval_card s (W / 2) W (by linarith) hs
  linarith

theorem odd_column_count (s : Finset ℤ) (x W : ℝ) (hW : 0 < W)
    (hxW : 40 ≤ x / W)
    (hs : ∀ d ∈ s, x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ d % 2 = 1) :
    (s.card : ℝ) ≤ 1.1 * x / (4 * W) := by
  have he : x / (2 * W) = (x / W) / 2 := by ring
  have hc := odd_integer_interval_card s (x / (2 * W)) (x / W) (by rw [he]; linarith) hs
  rw [he] at hc
  have he' : 1.1 * x / (4 * W) = 1.1 * (x / W) / 4 := by ring
  rw [he']
  linarith

/-- Combining both odd counts with the half-log coefficient gives the
exact 1.1/8 prefactor in the pointwise Type II estimate. -/
theorem typeII_counting_constant (C x W D N : ℝ) (hC : 0 ≤ C) (hx : 0 ≤ x)
    (hW : 40 ≤ W) (hD0 : 0 ≤ D) (hN0 : 0 ≤ N)
    (hD : D ≤ 1.1 * x / (4 * W)) (hN : N ≤ 1.1 * W / 4) :
    Real.sqrt (C * D * (N / 4 * Real.log W ^ 2)) ≤
      (1.1 / 8) * Real.sqrt (C * x) * Real.log W := by
  have hw : 0 < W := by linarith
  have hlog : 0 ≤ Real.log W := Real.log_nonneg (by linarith)
  have hprod : D * N ≤ (1.1 ^ 2 / 16) * x := by
    have hp := mul_le_mul hD hN hN0 (show 0 ≤ 1.1 * x / (4 * W) by positivity)
    have he : (1.1 * x / (4 * W)) * (1.1 * W / 4) = (1.1 ^ 2 / 16) * x := by
      field_simp
      <;> ring
    rwa [he] at hp
  have hb := mul_le_mul_of_nonneg_left hprod (show 0 ≤ C * Real.log W ^ 2 / 4 by positivity)
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hs := Real.sq_sqrt (mul_nonneg hC hx)
  nlinarith

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51OddBilinearPhase.lean
section

namespace TaoFivePrimes
open Finset

/-- Conjugation changes the sign of the frequency without changing the bound. -/
theorem unit_bilinear_block_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (N : ℕ) (t : ℝ) (a : ℕ → ℂ) (x : ι → ℂ) :
    ‖∑ j ∈ range N, a j *
      (∑ m, angularPhase ((2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * x m)‖ ≤
      Real.sqrt (((N : ℝ) + 2 * q - 1) * (∑ m, ‖x m‖ ^ 2) * ∑ j ∈ range N, ‖a j‖ ^ 2) := by
  have hb := unit_bilinear_block idx hinj q h hq hlo hhi hwidth N t
    (fun j => star (a j)) (fun m => star (x m))
  simp only [norm_star] at hb
  rw [← norm_star (∑ j ∈ range N, star (a j) *
    (∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * star (x m)))] at hb
  simp only [star_sum, star_mul, star_star, angularPhase_star] at hb
  have he (j : ℕ) (m : ι) : -((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) =
      (2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m := by ring
  simp only [he] at hb
  simpa only [mul_comm] using hb

/-- Exact phase identity for odd columns and consecutive odd rows. -/
lemma odd_bilinear_phase (alpha t : ℝ) (j : ℕ) (m : ℤ) :
    expCircle (alpha * ((2 * m + 1 : ℤ) : ℝ) * (2 * ((j : ℝ) + t))) =
      angularPhase ((2 * ((j : ℝ) + t) * (Real.pi * (4 * alpha))) * m) *
        expCircle (alpha * (2 * ((j : ℝ) + t))) := by
  unfold expCircle angularPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma expCircle_norm_one (t : ℝ) : ‖expCircle t‖ = 1 := by
  simp [expCircle, Complex.norm_exp]

/-- The actual e(alpha*d*w) kernel on odd columns and consecutive odd rows. -/
theorem unit_odd_bilinear_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q alpha : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ 4 * alpha) (hhi : 4 * alpha ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (N : ℕ) (t : ℝ) (a : ℕ → ℂ) (x : ι → ℂ) :
    ‖∑ j ∈ range N, a j *
      (∑ m, expCircle (alpha * ((2 * idx m + 1 : ℤ) : ℝ) *
        (2 * ((j : ℝ) + t))) * x m)‖ ≤
      Real.sqrt (((N : ℝ) + 2 * q - 1) * (∑ m, ‖x m‖ ^ 2) * ∑ j ∈ range N, ‖a j‖ ^ 2) := by
  have hb := unit_bilinear_block_positive idx hinj q (4 * alpha) hq hlo hhi hwidth N t
    (fun j => a j * expCircle (alpha * (2 * ((j : ℝ) + t)))) x
  simp only [norm_mul, expCircle_norm_one, mul_one] at hb
  convert hb using 1
  congr 1
  simp only [odd_bilinear_phase, mul_sum]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro m hm
  ring

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51OddRows.lean
section

namespace TaoFivePrimes
open Finset

lemma odd_rows_reindex {M : Type*} [AddCommMonoid M] (l u : ℤ) (F : ℤ → M) :
    (∑ w ∈ (Icc l u).image (fun n => 2 * n + 1), F w) =
      ∑ j ∈ range (u + 1 - l).toNat, F (2 * (l + (j : ℤ)) + 1) := by
  rw [sum_image (by intro a ha b hb hab; change 2 * a + 1 = 2 * b + 1 at hab; omega),
    Int.Icc_eq_finset_map, sum_map]
  rfl

lemma odd_rows_card (l u : ℤ) :
    ((Icc l u).image (fun n => 2 * n + 1)).card = (u + 1 - l).toNat := by
  rw [card_image_of_injective _ (by intro a b hab; change 2 * a + 1 = 2 * b + 1 at hab; omega), Int.card_Icc]

lemma mem_odd_rows (l u w : ℤ) :
    w ∈ (Icc l u).image (fun n => 2 * n + 1) ↔
      2 * l + 1 ≤ w ∧ w ≤ 2 * u + 1 ∧ w % 2 = 1 := by
  constructor
  · intro hw
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hw
    simp only [mem_Icc] at hn
    omega
  · intro hw
    apply mem_image.mpr
    refine ⟨w / 2, mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩ <;> omega

/-- Literal odd-row interval version, including an empty interval. -/
theorem unit_odd_rectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q alpha : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ 4 * alpha) (hhi : 4 * alpha ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (l u : ℤ) (a : ℤ → ℂ) (x : ι → ℂ) :
    ‖∑ w ∈ (Icc l u).image (fun n => 2 * n + 1), a w *
      (∑ m, expCircle (alpha * ((2 * idx m + 1 : ℤ) : ℝ) * w) * x m)‖ ≤
      Real.sqrt (((((Icc l u).image (fun n => 2 * n + 1)).card : ℝ) + 2 * q - 1) *
        (∑ m, ‖x m‖ ^ 2) * ∑ w ∈ (Icc l u).image (fun n => 2 * n + 1), ‖a w‖ ^ 2) := by
  rw [odd_rows_card, odd_rows_reindex, odd_rows_reindex]
  have hb := unit_odd_bilinear_block idx hinj q alpha hq hlo hhi hwidth
    (u + 1 - l).toNat ((l : ℝ) + 1 / 2) (fun j => a (2 * (l + (j : ℤ)) + 1)) x
  have he (j : ℕ) : ((2 * (l + (j : ℤ)) + 1 : ℤ) : ℝ) =
      2 * ((j : ℝ) + ((l : ℝ) + 1 / 2)) := by push_cast; ring
  simpa only [he] using hb

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51CoefficientEnergy.lean
section

namespace TaoFivePrimes
open Finset

/-- The half-log bound for the exact coefficient in the public Type II sum. -/
theorem theorem51Centered_abs_le (V : ℝ) (w : ℕ) :
    |theorem51Centered V w| ≤ Real.log w / 2 := by
  have hlo : 0 ≤ ∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)),
      ArithmeticFunction.vonMangoldt b :=
    sum_nonneg fun b hb => ArithmeticFunction.vonMangoldt_nonneg
  have hhi : (∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)),
      ArithmeticFunction.vonMangoldt b) ≤ Real.log w := by
    rw [← ArithmeticFunction.vonMangoldt_sum]
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro b hb hb'
    exact ArithmeticFunction.vonMangoldt_nonneg
  unfold theorem51Centered
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem theorem51Centered_energy (s : Finset ℕ) (V W : ℝ) (hW : 1 ≤ W)
    (hs : ∀ w ∈ s, 0 < w ∧ (w : ℝ) ≤ W) :
    (∑ w ∈ s, ‖(theorem51Centered V w : ℂ)‖ ^ 2) ≤
      (s.card : ℝ) * (Real.log W / 2) ^ 2 := by
  calc
    _ ≤ ∑ w ∈ s, (Real.log W / 2) ^ 2 := by
      apply sum_le_sum
      intro w hw
      apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.log_nonneg hW) (by norm_num))).mpr
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hh := theorem51Centered_abs_le V w
      have hl := Real.log_le_log (by exact_mod_cast (hs w hw).1) (hs w hw).2
      linarith
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

theorem moebius_coefficient_energy (s : Finset ℕ) :
    (∑ d ∈ s, ‖(ArithmeticFunction.moebius d : ℂ)‖ ^ 2) ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ d ∈ s, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      have h : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      nlinarith [norm_nonneg (ArithmeticFunction.moebius d : ℂ)]
    _ = _ := by simp

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51ColumnPartition.lean
section

namespace TaoFivePrimes
open Finset

/-- Consecutive full blocks enumerate a finite range exactly once. -/
theorem range_blocks_sum {A : Type*} [AddCommMonoid A]
    (K M : ℕ) (F : ℕ → A) :
    (∑ b ∈ range K, ∑ m ∈ range M, F (b * M + m)) = ∑ n ∈ range (K * M), F n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih, Nat.succ_mul, sum_range_add]

/-- Padding only beyond the end of the original range preserves its sum. -/
theorem range_blocks_zero_pad {A : Type*} [AddCommMonoid A]
    (D K M : ℕ) (hcover : D ≤ K * M) (F : ℕ → A) :
    (∑ b ∈ range K, ∑ m ∈ range M, if b * M + m < D then F (b * M + m) else 0) =
      ∑ n ∈ range D, F n := by
  rw [range_blocks_sum K M (fun n => if n < D then F n else 0)]
  symm
  calc
    _ = ∑ n ∈ range D, if n < D then F n else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [if_pos (mem_range.mp hn)]
    _ = ∑ n ∈ range (K * M), if n < D then F n else 0 := by
      apply sum_subset (range_mono hcover)
      intro n hn hnD
      exact if_neg (by simpa only [mem_range] using hnD)

/-- Integer interval subdivision, valid also when the interval is empty. -/
theorem integer_interval_blocks {A : Type*} [AddCommMonoid A]
    (l u : ℤ) (K M : ℕ) (hcover : (u + 1 - l).toNat ≤ K * M) (F : ℤ → A) :
    (∑ b ∈ range K, ∑ m ∈ range M,
      if l + ((b * M + m : ℕ) : ℤ) ≤ u then F (l + ((b * M + m : ℕ) : ℤ)) else 0) =
      ∑ n ∈ Icc l u, F n := by
  rw [Int.Icc_eq_finset_map, sum_map]
  change _ = ∑ n ∈ range (u + 1 - l).toNat, F (l + (n : ℤ))
  have hb := range_blocks_zero_pad (u + 1 - l).toNat K M hcover (fun n => F (l + (n : ℤ)))
  convert hb using 1
  apply sum_congr rfl
  intro b hb
  apply sum_congr rfl
  intro m hm
  have he : l + ((b * M + m : ℕ) : ℤ) ≤ u ↔ b * M + m < (u + 1 - l).toNat := by omega
  simp only [he]

theorem integer_interval_blocks_energy (l u : ℤ) (K M : ℕ)
    (hcover : (u + 1 - l).toNat ≤ K * M) (c : ℤ → ℂ) :
    (∑ b ∈ range K, ∑ m ∈ range M,
      ‖if l + ((b * M + m : ℕ) : ℤ) ≤ u then c (l + ((b * M + m : ℕ) : ℤ)) else 0‖ ^ 2) =
      ∑ n ∈ Icc l u, ‖c n‖ ^ 2 := by
  have hb := integer_interval_blocks l u K M hcover (fun n => ‖c n‖ ^ 2)
  simpa only [apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero, zero_pow (by decide : 2 ≠ 0)] using hb

/-- This many full blocks cover the interval; the same formula handles an
empty interval through zero padding. -/
theorem integer_block_cover (l u : ℤ) (M : ℕ) (hM : 0 < M) :
    (u + 1 - l).toNat ≤ ((u - l).toNat / M + 1) * M := by
  have hd := Nat.mod_lt (u - l).toNat hM
  have he := Nat.mod_add_div (u - l).toNat M
  rw [Nat.mul_comm M] at he
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem integer_block_count (l u : ℤ) (M : ℕ) (q L : ℝ) (hq : 0 < q)
    (hL : 0 ≤ L) (hsize : q / 2 ≤ (M : ℝ)) (hspan : (u : ℝ) - (l : ℝ) ≤ L) :
    (((u - l).toNat / M + 1 : ℕ) : ℝ) ≤ 2 * L / q + 1 := by
  have hspan' : ((u - l).toNat : ℝ) ≤ L := by
    by_cases hh : 0 ≤ u - l
    · have he : ((u - l).toNat : ℝ) = (u : ℝ) - (l : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg hh)
      rwa [he]
    · rw [Int.toNat_eq_zero.mpr (by omega), Nat.cast_zero]
      exact hL
  have hd : (((u - l).toNat / M : ℕ) : ℝ) * M ≤ ((u - l).toNat : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (u - l).toNat M
  have hm := mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg ((u - l).toNat / M) :
    (0 : ℝ) ≤ ((u - l).toNat / M : ℕ))
  have hb : (((u - l).toNat / M : ℕ) : ℝ) ≤ 2 * L / q := by
    apply (le_div_iff₀ hq).mpr
    nlinarith
  push_cast
  linarith

theorem half_modulus_block_size (q : ℕ) :
    (q : ℝ) / 2 ≤ (((q + 1) / 2 : ℕ) : ℝ) ∧
      (((q + 1) / 2 : ℕ) : ℝ) - 1 ≤ (q : ℝ) / 2 := by
  have hlo : q ≤ 2 * ((q + 1) / 2) := by omega
  have hhi : 2 * ((q + 1) / 2) ≤ q + 1 := by omega
  have hloR : (q : ℝ) ≤ 2 * (((q + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hlo
  have hhiR : 2 * (((q + 1) / 2 : ℕ) : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hhi
  constructor <;> linarith

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51PaddedRectangle.lean
section

namespace TaoFivePrimes
open Finset

/-- The concrete column partition feeds the bilinear estimate and preserves
the original coefficient energy. -/
theorem unit_padded_odd_rectangle (q alpha : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ 4 * alpha) (hhi : 4 * alpha ≤ (q + 1) / q ^ 2)
    (L R l u : ℤ) (K M : ℕ) (hcover : (R + 1 - L).toNat ≤ K * M)
    (hsize : (M : ℝ) - 1 ≤ q / 2) (a c : ℤ → ℂ) :
    ‖∑ w ∈ (Icc l u).image (fun n => 2 * n + 1), a w *
      (∑ n ∈ Icc L R, expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * c n)‖ ≤
      Real.sqrt ((K : ℝ) *
        (((((Icc l u).image (fun n => 2 * n + 1)).card : ℝ) + 2 * q - 1) *
          (∑ n ∈ Icc L R, ‖c n‖ ^ 2)) *
        ∑ w ∈ (Icc l u).image (fun n => 2 * n + 1), ‖a w‖ ^ 2) := by
  let idx (b : ℕ) (m : Fin M) : ℤ := L + ((b * M + m.val : ℕ) : ℤ)
  let cp (b : ℕ) (m : Fin M) : ℂ := if idx b m ≤ R then c (idx b m) else 0
  let rows := (Icc l u).image (fun n => 2 * n + 1)
  let F (b : ℕ) : ℂ := ∑ w ∈ rows, a w *
    (∑ m : Fin M, expCircle (alpha * ((2 * idx b m + 1 : ℤ) : ℝ) * w) * cp b m)
  have hinj (b : ℕ) : Function.Injective (idx b) := by
    intro m n he
    apply Fin.ext
    dsimp [idx] at he
    omega
  have hwidth (b : ℕ) (m n : Fin M) : |(idx b m : ℝ) - (idx b n : ℝ)| ≤ q / 2 := by
    have hm : (m.val : ℝ) + 1 ≤ M := by exact_mod_cast m.isLt
    have hn : (n.val : ℝ) + 1 ≤ M := by exact_mod_cast n.isLt
    have hm0 : (0 : ℝ) ≤ m.val := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ n.val := Nat.cast_nonneg _
    dsimp [idx]
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have henergy : (∑ b ∈ range K, ∑ m : Fin M, ‖cp b m‖ ^ 2) = ∑ n ∈ Icc L R, ‖c n‖ ^ 2 := by
    have he := integer_interval_blocks_energy L R K M hcover c
    conv_lhs at he => arg 2; ext b; rw [← Fin.sum_univ_eq_sum_range]
    exact he
  have hinner (w : ℤ) :
      (∑ n ∈ Icc L R, expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * c n) =
      ∑ b ∈ range K, ∑ m : Fin M,
        expCircle (alpha * ((2 * idx b m + 1 : ℤ) : ℝ) * w) * cp b m := by
    have he := integer_interval_blocks L R K M hcover
      (fun n => expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * c n)
    conv_lhs at he => arg 2; ext b; rw [← Fin.sum_univ_eq_sum_range]
    simpa only [cp, idx, mul_ite, mul_zero] using he.symm
  have hsum : (∑ w ∈ rows, a w *
      (∑ n ∈ Icc L R, expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * c n)) =
      ∑ b ∈ range K, F b := by
    simp only [hinner, mul_sum, F]
    rw [sum_comm]
  let C : ℝ := (rows.card : ℝ) + 2 * q - 1
  let E : ℝ := ∑ w ∈ rows, ‖a w‖ ^ 2
  have hb (b : ℕ) : ‖F b‖ ^ 2 ≤ C * (∑ m : Fin M, ‖cp b m‖ ^ 2) * E := by
    have hh := unit_odd_rectangle (idx b) (hinj b) q alpha hq hlo hhi (hwidth b) l u a (cp b)
    have hC : 0 ≤ C := by dsimp [C]; have hc := Nat.cast_nonneg rows.card (α := ℝ); linarith
    have hE : 0 ≤ E := sum_nonneg fun w hw => sq_nonneg _
    exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg
      (mul_nonneg hC (sum_nonneg fun m hm => sq_nonneg _)) hE)).mp hh
  change ‖∑ w ∈ rows, a w * _‖ ≤ _
  rw [hsum]
  apply Real.le_sqrt_of_sq_le
  apply (complex_sum_sq_le_card_energy (range K) F).trans
  have hh := sum_le_sum (s := range K) (fun b hb' => hb b)
  have hmul := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  rw [← sum_mul, ← mul_sum, henergy] at hmul
  simpa only [card_range, C, E, rows, mul_assoc] using hmul

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51ScaleIntervals.lean
section

namespace TaoFivePrimes
open Finset

lemma mem_oddHalfInterval (A B : ℝ) (n : ℤ) :
    n ∈ oddHalfInterval A B ↔ A ≤ ((2 * n + 1 : ℤ) : ℝ) ∧
      ((2 * n + 1 : ℤ) : ℝ) ≤ B := by
  simp only [oddHalfInterval, mem_Icc, Int.ceil_le, Int.le_floor,
    Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
  constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith

lemma mem_oddRealInterval (A B : ℝ) (w : ℤ) :
    w ∈ oddRealInterval A B ↔ A ≤ (w : ℝ) ∧ (w : ℝ) ≤ B ∧ w % 2 = 1 := by
  constructor
  · intro hw
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hw
    have hh := (mem_oddHalfInterval A B n).mp hn
    exact ⟨hh.1, hh.2, by omega⟩
  · intro hw
    have he : 2 * (w / 2) + 1 = w := by omega
    apply mem_image.mpr
    refine ⟨w / 2, (mem_oddHalfInterval A B _).mpr ?_, he⟩
    rw [he]
    exact ⟨hw.1, hw.2.1⟩

lemma odd_interval_card_eq (A B : ℝ) :
    (oddRealInterval A B).card = (oddHalfInterval A B).card := by
  apply card_image_of_injective
  intro m n he
  change 2 * m + 1 = 2 * n + 1 at he
  omega

lemma odd_half_span (A B : ℝ) :
    (⌊(B - 1) / 2⌋ : ℝ) - (⌈(A - 1) / 2⌉ : ℝ) ≤ (B - A) / 2 := by
  have hB := Int.floor_le ((B - 1) / 2)
  have hA := Int.le_ceil ((A - 1) / 2)
  linarith

lemma odd_real_interval_count (A B : ℝ) (hAB : A ≤ B) :
    ((oddRealInterval A B).card : ℝ) ≤ (B - A) / 2 + 1 :=
  odd_integer_interval_card _ A B hAB (fun w hw => (mem_oddRealInterval A B w).mp hw)

lemma scale_row_counts (W : ℝ) (hW : 40 ≤ W) :
    ((oddRealInterval (W / 2) W).card : ℝ) - 1 ≤ W / 4 ∧
      ((oddRealInterval (W / 2) W).card : ℝ) ≤ 1.1 * W / 4 := by
  have hc := odd_real_interval_count (W / 2) W (by linarith)
  constructor <;> linarith

lemma scale_column_count (x W : ℝ) (hW : 0 < W) (hxW : 40 ≤ x / W) :
    ((oddHalfInterval (x / (2 * W)) (x / W)).card : ℝ) ≤ 1.1 * x / (4 * W) := by
  rw [← odd_interval_card_eq]
  exact odd_column_count _ x W hW hxW (fun d hd =>
    (mem_oddRealInterval (x / (2 * W)) (x / W) d).mp hd)

lemma scale_column_block_count (x W : ℝ) (q : ℕ) (hW : 0 < W) (hx : 0 ≤ x)
    (hq : 0 < q) :
    ((((⌊(x / W - 1) / 2⌋ - ⌈(x / (2 * W) - 1) / 2⌉ : ℤ).toNat /
      ((q + 1) / 2)) + 1 : ℕ) : ℝ) ≤ x / (2 * W * q) + 1 := by
  have hspan := odd_half_span (x / (2 * W)) (x / W)
  have he : (x / W - x / (2 * W)) / 2 = x / (4 * W) := by ring
  rw [he] at hspan
  have hb := integer_block_count ⌈(x / (2 * W) - 1) / 2⌉ ⌊(x / W - 1) / 2⌋
    ((q + 1) / 2) q (x / (4 * W)) (by exact_mod_cast hq)
    (by positivity) (half_modulus_block_size q).1 hspan
  have he' : 2 * (x / (4 * W)) / (q : ℝ) + 1 = x / (2 * W * q) + 1 := by ring
  rwa [he'] at hb

end TaoFivePrimes



end


-- Source: examples/five-primes/Theorem51ScaleCoefficients.lean
section

namespace TaoFivePrimes
open Finset

lemma scale_column_energy (s : Finset ℤ) (U : ℝ) :
    (∑ n ∈ s, ‖scaleColumnCoefficient U n‖ ^ 2) ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ n ∈ s, (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      unfold scaleColumnCoefficient
      split_ifs
      · have h : ‖(ArithmeticFunction.moebius (2 * n + 1).toNat : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := (2 * n + 1).toNat))
        nlinarith [norm_nonneg (ArithmeticFunction.moebius (2 * n + 1).toNat : ℂ)]
      · norm_num
    _ = _ := by simp

lemma scale_row_energy (V W : ℝ) (hW : 40 ≤ W) :
    (∑ w ∈ oddRealInterval (W / 2) W, ‖scaleRowCoefficient V w‖ ^ 2) ≤
      ((oddRealInterval (W / 2) W).card : ℝ) * (Real.log W / 2) ^ 2 := by
  calc
    _ ≤ ∑ w ∈ oddRealInterval (W / 2) W, (Real.log W / 2) ^ 2 := by
      apply sum_le_sum
      intro w hw
      have hh := (mem_oddRealInterval (W / 2) W w).mp hw
      have hw0 : 0 ≤ w := by exact_mod_cast (show (0 : ℝ) ≤ w by linarith)
      have he : (w.toNat : ℝ) = (w : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg hw0)
      unfold scaleRowCoefficient
      split_ifs
      · apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.log_nonneg (by linarith)) (by norm_num))).mpr
        rw [Complex.norm_real, Real.norm_eq_abs]
        have hb := theorem51Centered_abs_le V w.toNat
        have hl : Real.log (w.toNat : ℝ) ≤ Real.log W := by
          apply Real.log_le_log
          · rw [he]; linarith
          · rw [he]; exact hh.2.1
        linarith
      · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

end TaoFivePrimes


end


-- Source: examples/five-primes/Theorem51ScaleBound.lean
section

namespace TaoFivePrimes
open Finset

theorem theorem51_scale_bound_positive (x alpha U V W : ℝ) (q : ℕ)
    (hq : 100 ≤ q) (hW : 40 ≤ W) (hxW : 40 ≤ x / W)
    (hlo : ((q : ℝ) - 1) / (q : ℝ) ^ 2 ≤ 4 * alpha)
    (hhi : 4 * alpha ≤ ((q : ℝ) + 1) / (q : ℝ) ^ 2) :
    ‖theorem51ScaleSum x alpha U V W‖ ≤
      (1.1 / 8) * Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) * Real.log W := by
  have hw : 0 < W := by linarith
  have hx : 0 ≤ x := by
    have hh := (le_div_iff₀ hw).mp hxW
    nlinarith
  have hq0 : 0 < q := by omega
  have hqr : (100 : ℝ) ≤ q := by exact_mod_cast hq
  let L : ℤ := ⌈(x / (2 * W) - 1) / 2⌉
  let R : ℤ := ⌊(x / W - 1) / 2⌋
  let M : ℕ := (q + 1) / 2
  let K : ℕ := (R - L).toNat / M + 1
  let D : ℝ := (oddHalfInterval (x / (2 * W)) (x / W)).card
  let N : ℝ := (oddRealInterval (W / 2) W).card
  let C : ℝ := (W / 4 + 2 * q) * (x / (2 * W * q) + 1)
  have hM : 0 < M := by dsimp [M]; omega
  have hb := unit_padded_odd_rectangle q alpha hqr hlo hhi L R
    ⌈(W / 2 - 1) / 2⌉ ⌊(W - 1) / 2⌋ K M
    (integer_block_cover L R M hM) (half_modulus_block_size q).2
    (scaleRowCoefficient V) (scaleColumnCoefficient U)
  change ‖theorem51ScaleSum x alpha U V W‖ ≤
    Real.sqrt ((K : ℝ) * ((N + 2 * q - 1) *
      (∑ n ∈ oddHalfInterval (x / (2 * W)) (x / W), ‖scaleColumnCoefficient U n‖ ^ 2)) *
      ∑ w ∈ oddRealInterval (W / 2) W, ‖scaleRowCoefficient V w‖ ^ 2) at hb
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hfactor : 0 ≤ N + 2 * q - 1 := by linarith
  have hk := scale_column_block_count x W q hw hx hq0
  change (K : ℝ) ≤ x / (2 * W * q) + 1 at hk
  have hn := scale_row_counts W hW
  have hc : (K : ℝ) * (N + 2 * q - 1) ≤ C := by
    have ht : N + 2 * q - 1 ≤ W / 4 + 2 * q := by linarith [hn.1]
    have hm := mul_le_mul hk ht hfactor (by positivity : 0 ≤ x / (2 * W * q) + 1)
    dsimp [C]
    nlinarith
  have hd := scale_column_energy (oddHalfInterval (x / (2 * W)) (x / W)) U
  have ha := scale_row_energy V W hW
  have he : (K : ℝ) * ((N + 2 * q - 1) *
      (∑ n ∈ oddHalfInterval (x / (2 * W)) (x / W), ‖scaleColumnCoefficient U n‖ ^ 2)) *
      (∑ w ∈ oddRealInterval (W / 2) W, ‖scaleRowCoefficient V w‖ ^ 2) ≤
      C * D * (N / 4 * Real.log W ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hd (mul_nonneg (Nat.cast_nonneg K) hfactor)
    have h2 := mul_le_mul_of_nonneg_right hc hD0
    have h3 := mul_le_mul (h1.trans h2) ha (sum_nonneg (fun _ _ => sq_nonneg _))
      (mul_nonneg hC0 hD0)
    convert h3 using 2 <;> first | rfl | ring
  exact hb.trans ((Real.sqrt_le_sqrt he).trans
    (typeII_counting_constant C x W D N hC0 hx hW hD0 hN0
      (scale_column_count x W hw hxW) hn.2))

end TaoFivePrimes







end


-- Source: examples/five-primes/Theorem51ScaleSigned.lean
section

namespace TaoFivePrimes
open Finset

lemma expCircle_neg_conjugate (t : ℝ) :
    expCircle (-t) = star (expCircle t) := by
  rw [expCircle, expCircle, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

lemma theorem51ScaleSum_neg (x alpha U V W : ℝ) :
    theorem51ScaleSum x (-alpha) U V W = star (theorem51ScaleSum x alpha U V W) := by
  unfold theorem51ScaleSum
  simp only [star_sum, star_mul, mul_comm]
  apply sum_congr rfl
  intro w hw
  have hr : star (scaleRowCoefficient V w) = scaleRowCoefficient V w := by
    unfold scaleRowCoefficient
    split_ifs <;> simp
  rw [hr]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hc : star (scaleColumnCoefficient U n) = scaleColumnCoefficient U n := by
    unfold scaleColumnCoefficient
    split_ifs <;> simp
  rw [hc, ← expCircle_neg_conjugate]
  congr 2
  ring

theorem theorem51_scale_bound_signed (x alpha beta U V W : ℝ) (a : ℤ) (q : ℕ)
    (hq : 100 ≤ q) (hW : 40 ≤ W) (hxW : 40 ≤ x / W)
    (ha : a.natAbs = 1) (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    ‖theorem51ScaleSum x alpha U V W‖ ≤
      (1.1 / 8) * Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) * Real.log W := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have he1 : 1 / (q : ℝ) - 1 / (q : ℝ) ^ 2 = ((q : ℝ) - 1) / (q : ℝ) ^ 2 := by
    field_simp <;> ring
  have he2 : 1 / (q : ℝ) + 1 / (q : ℝ) ^ 2 = ((q : ℝ) + 1) / (q : ℝ) ^ 2 := by
    field_simp <;> ring
  have hb := abs_le.mp hbeta
  have haa : a = 1 ∨ a = -1 := by omega
  rcases haa with rfl | rfl
  · simp only [Int.cast_one, Int.cast_neg, neg_div] at halpha
    apply theorem51_scale_bound_positive x alpha U V W q hq hW hxW
    · rw [← he1]; linarith
    · rw [← he2]; linarith
  · simp only [Int.cast_one, Int.cast_neg, neg_div] at halpha
    have hh := theorem51_scale_bound_positive x (-alpha) U V W q hq hW hxW
      (by rw [← he1]; linarith) (by rw [← he2]; linarith)
    simpa [theorem51ScaleSum_neg] using hh

end TaoFivePrimes



end


-- Source: examples/five-primes/Theorem51ScaleIntegrals.lean
section

namespace TaoFivePrimes
open MeasureTheory

/-- The logarithmic weight is integrated against dW/W. -/
lemma integral_log_div_positive (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log t / t) =
      ((Real.log b) ^ 2 - (Real.log a) ^ 2) / 2 := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => Real.log t / t) (Set.Icc a b) :=
    (continuousOn_id.log (fun t ht => (hpos t ht).ne')).div continuousOn_id
      (fun t ht => (hpos t ht).ne')
  have hi : IntervalIntegrable (fun t : ℝ => Real.log t / t) volume a b := hc.intervalIntegrable_of_Icc hab
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => (Real.log t) ^ 2 / 2) (Real.log t / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    convert ((Real.hasDerivAt_log (hpos t ht).ne').pow 2).div_const 2 using 1 <;> first | rfl | ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  convert he using 1 <;> first | rfl | ring

lemma integral_log_div_factorized (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log t / t) = Real.log (b / a) * Real.log (a * b) / 2 := by
  have hb : 0 < b := ha.trans_le hab
  rw [integral_log_div_positive a b ha hab, Real.log_div hb.ne' ha.ne',
    Real.log_mul ha.ne' hb.ne']
  ring

end TaoFivePrimes



end


-- Source: examples/five-primes/Theorem51ScaleSupport.lean
section

namespace TaoFivePrimes
open Finset

lemma theorem51ScaleSum_zero_below (x alpha U V W : ℝ) (hWV : W ≤ V) :
    theorem51ScaleSum x alpha U V W = 0 := by
  unfold theorem51ScaleSum
  apply sum_eq_zero
  intro w hw
  have hh := (mem_oddRealInterval (W / 2) W w).mp hw
  simp [scaleRowCoefficient, not_lt.mpr (hh.2.1.trans hWV)]

lemma theorem51ScaleSum_zero_above (x alpha U V W : ℝ)
    (hU : 0 < U) (hW : 0 < W) (hUW : x / U ≤ W) :
    theorem51ScaleSum x alpha U V W = 0 := by
  have hx : x / W ≤ U := by
    apply (div_le_iff₀ hW).mpr
    have hh := (div_le_iff₀ hU).mp hUW
    nlinarith
  unfold theorem51ScaleSum
  apply sum_eq_zero
  intro w hw
  have hz : (∑ n ∈ oddHalfInterval (x / (2 * W)) (x / W),
      expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * scaleColumnCoefficient U n) = 0 := by
    apply sum_eq_zero
    intro n hn
    have hh := (mem_oddHalfInterval (x / (2 * W)) (x / W) n).mp hn
    simp only [scaleColumnCoefficient, if_neg (not_lt.mpr (hh.2.trans hx)), mul_zero]
  rw [hz, mul_zero]

end TaoFivePrimes


end


-- Source: examples/five-primes/Theorem51EtaScale.lean
section

namespace TaoFivePrimes
open MeasureTheory

/-- The cutoff is the logarithmic length of the overlap of two scale windows. -/
lemma eta0_log_overlap (r w : ℝ) (hr : 0 < r) (hw : 0 < w) :
    eta0 (w / r) =
      if max w (r / 2) < min (2 * w) r then
        4 * Real.log (min (2 * w) r / max w (r / 2)) else 0 := by
  by_cases hlow : w ≤ r / 4
  · rw [eta0_zero_below_quarter ((div_le_iff₀ hr).mpr (by linarith))]
    have hh : ¬ max w (r / 2) < min (2 * w) r := by
      have h1 := le_max_right w (r / 2)
      have h2 := min_le_left (2 * w) r
      linarith
    rw [if_neg hh]
  · by_cases hmid : w ≤ r / 2
    · have htlo : 1 / 4 ≤ w / r := (le_div_iff₀ hr).mpr (by linarith)
      have hthi : w / r ≤ 1 / 2 := (div_le_iff₀ hr).mpr (by linarith)
      rw [eta0_lower_piece htlo hthi, max_eq_right hmid,
        min_eq_left (by linarith : 2 * w ≤ r), if_pos (by linarith)]
      congr 2
      ring
    · by_cases hhigh : w < r
      · have htlo : 1 / 2 ≤ w / r := (le_div_iff₀ hr).mpr (by linarith)
        have hthi : w / r ≤ 1 := (div_le_iff₀ hr).mpr (by linarith)
        rw [eta0_upper_piece htlo hthi, max_eq_left (by linarith : r / 2 ≤ w),
          min_eq_right (by linarith : r ≤ 2 * w), if_pos hhigh,
          Real.log_div hr.ne' hw.ne', Real.log_div hw.ne' hr.ne']
        ring
      · rw [eta0_zero_above_one ((le_div_iff₀ hr).mpr (by linarith))]
        have hh : ¬ max w (r / 2) < min (2 * w) r := by
          have h1 := le_max_left w (r / 2)
          have h2 := min_le_right (2 * w) r
          linarith
        rw [if_neg hh]

lemma integral_inv_Icc_positive (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Set.Icc a b, (t : ℝ)⁻¹) = if a < b then Real.log (b / a) else 0 := by
  by_cases hab : a < b
  · rw [if_pos hab, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab.le, integral_inv_of_pos ha hb]
  · rw [if_neg hab]
    rcases lt_or_eq_of_le (le_of_not_gt hab) with hba | rfl
    · simp [Set.Icc_eq_empty_of_lt hba]
    · simp

lemma eta0_scale_integral (r w : ℝ) (hr : 0 < r) (hw : 0 < w) :
    eta0 (w / r) =
      4 * ∫ W in Set.Icc (max w (r / 2)) (min (2 * w) r), (W : ℝ)⁻¹ := by
  rw [integral_inv_Icc_positive _ _ (lt_of_lt_of_le hw (le_max_left _ _))
    (lt_min (by positivity) hr), eta0_log_overlap r w hr hw]
  split_ifs <;> simp

lemma scale_pair_mem (x d w W : ℝ) (hd : 0 < d) (hw : 0 < w) :
    (x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W) ↔
      W ∈ Set.Icc (max w (x / d / 2)) (min (2 * w) (x / d)) := by
  simp only [Set.mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hW : 0 < W := hw.trans_le h4
    have ha := (div_le_iff₀ (show 0 < 2 * W by positivity)).mp h1
    have hb := (le_div_iff₀ hW).mp h2
    refine ⟨⟨h4, ?_⟩, ⟨by linarith, ?_⟩⟩
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      apply (div_le_iff₀ hd).mpr
      nlinarith
    · apply (le_div_iff₀ hd).mpr
      nlinarith
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hW : 0 < W := hw.trans_le h1
    have ha := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp h2
    have hb := (div_le_iff₀ hd).mp ha
    have hc := (le_div_iff₀ hd).mp h4
    refine ⟨?_, ?_, by linarith, h1⟩
    · apply (div_le_iff₀ (show 0 < 2 * W by positivity)).mpr
      nlinarith
    · apply (le_div_iff₀ hW).mpr
      nlinarith

/-- A single actual (d,w) summand has precisely the required scale integral. -/
lemma eta0_pair_scale_integral (x d w : ℝ) (hx : 0 < x) (hd : 0 < d) (hw : 0 < w) :
    eta0 (d * w / x) = 4 * ∫ W : ℝ,
      if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then W⁻¹ else 0 := by
  have he : (fun W : ℝ =>
      if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then W⁻¹ else 0) =
      (Set.Icc (max w (x / d / 2)) (min (2 * w) (x / d))).indicator (fun W : ℝ => W⁻¹) := by
    funext W
    simp only [Set.indicator, scale_pair_mem x d w W hd hw]
  rw [he, integral_indicator measurableSet_Icc]
  have hh := eta0_scale_integral (x / d) w (div_pos hx hd) hw
  have ht : w / (x / d) = d * w / x := by field_simp <;> ring
  rwa [ht] at hh

lemma scale_pair_integrable (x d w : ℝ) (hd : 0 < d) (hw : 0 < w) :
    Integrable (fun W : ℝ =>
      if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then W⁻¹ else 0) := by
  have he : (fun W : ℝ =>
      if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then W⁻¹ else 0) =
      (Set.Icc (max w (x / d / 2)) (min (2 * w) (x / d))).indicator (fun W : ℝ => W⁻¹) := by
    funext W
    simp only [Set.indicator, scale_pair_mem x d w W hd hw]
  rw [he, integrable_indicator_iff measurableSet_Icc]
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply continuousOn_id.inv₀
  intro W hW
  exact (hw.trans_le ((le_max_left _ _).trans hW.1)).ne'

lemma eta0_pair_scale_integral_complex (x d w : ℝ) (c : ℂ)
    (hx : 0 < x) (hd : 0 < d) (hw : 0 < w) :
    c * (eta0 (d * w / x) : ℂ) = 4 * ∫ W : ℝ, c *
      ((if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then W⁻¹ else 0 : ℝ) : ℂ) := by
  rw [integral_const_mul, integral_complex_ofReal, eta0_pair_scale_integral x d w hx hd hw]
  push_cast
  ring

/-- Finite-sum/interchange version of the actual pairwise scale decomposition. -/
lemma finite_eta0_scale_integral {ι : Type*} (s : Finset ι) (x : ℝ)
    (d w : ι → ℝ) (c : ι → ℂ) (hx : 0 < x)
    (hd : ∀ i ∈ s, 0 < d i) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, c i * (eta0 (d i * w i / x) : ℂ)) =
      4 * ∫ W : ℝ, ∑ i ∈ s, c i *
        ((if x / (2 * W) ≤ d i ∧ d i ≤ x / W ∧ W / 2 ≤ w i ∧ w i ≤ W
          then W⁻¹ else 0 : ℝ) : ℂ) := by
  let F (i : ι) (W : ℝ) : ℂ := c i *
    ((if x / (2 * W) ≤ d i ∧ d i ≤ x / W ∧ W / 2 ≤ w i ∧ w i ≤ W
      then W⁻¹ else 0 : ℝ) : ℂ)
  have hint (i : ι) (hi : i ∈ s) : Integrable (F i) :=
    ((scale_pair_integrable x (d i) (w i) (hd i hi) (hw i hi)).ofReal).const_mul (c i)
  calc
    _ = ∑ i ∈ s, (4 : ℂ) * ∫ W, F i W := by
      apply Finset.sum_congr rfl
      intro i hi
      exact eta0_pair_scale_integral_complex x (d i) (w i) (c i) hx (hd i hi) (hw i hi)
    _ = 4 * ∑ i ∈ s, ∫ W, F i W := (Finset.mul_sum s _ 4).symm
    _ = _ := by
      congr 1
      exact (integral_finsetSum s hint).symm

end TaoFivePrimes


end


-- Source: examples/five-primes/Theorem51TypeIIFinite.lean
section

namespace TaoFivePrimes
open Finset

noncomputable def theorem51TypeIISummand (x alpha U V : ℝ) (d w : ℕ) : ℂ :=
  if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
    (ArithmeticFunction.moebius d : ℂ) * (theorem51Centered V w : ℂ) *
      expCircle (alpha * d * w) * (eta0 ((d : ℝ) * w / x) : ℂ)
  else 0

lemma theorem51TypeIISummand_zero_outside (x alpha U V : ℝ) (d w : ℕ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hout : d ∉ Icc 1 ⌈x⌉₊ ∨ w ∉ Icc 1 ⌈x⌉₊) :
    theorem51TypeIISummand x alpha U V d w = 0 := by
  unfold theorem51TypeIISummand
  split_ifs with h
  · have hd1 : (1 : ℝ) ≤ d := by linarith [h.1]
    have hw1 : (1 : ℝ) ≤ w := by linarith [h.2.1]
    have hdn : 1 ≤ d := by exact_mod_cast hd1
    have hwn : 1 ≤ w := by exact_mod_cast hw1
    have hlarge : x < (d : ℝ) ∨ x < (w : ℝ) := by
      rcases hout with hd | hw
      · have hh : ⌈x⌉₊ < d := by simp only [mem_Icc] at hd; omega
        have hc : (⌈x⌉₊ : ℝ) < d := by exact_mod_cast hh
        exact Or.inl ((Nat.le_ceil x).trans_lt hc)
      · have hh : ⌈x⌉₊ < w := by simp only [mem_Icc] at hw; omega
        have hc : (⌈x⌉₊ : ℝ) < w := by exact_mod_cast hh
        exact Or.inr ((Nat.le_ceil x).trans_lt hc)
    have he : eta0 ((d : ℝ) * w / x) = 0 := by
      apply eta0_zero_above_one
      apply (le_div_iff₀ hx).mpr
      rcases hlarge with hd | hw
      · nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity) (sub_nonneg.mpr hw1)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (show (0 : ℝ) ≤ w by positivity)]
    rw [he, Complex.ofReal_zero, mul_zero]
  · rfl

/-- The public double tsum is exactly a finite rectangle in the positive regime. -/
lemma theorem51TypeII_finite (x alpha U V : ℝ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    theorem51TypeII x alpha U V =
      ‖∑ d ∈ Icc 1 ⌈x⌉₊, ∑ w ∈ Icc 1 ⌈x⌉₊, theorem51TypeIISummand x alpha U V d w‖ := by
  change ‖∑' d : ℕ, ∑' w : ℕ, theorem51TypeIISummand x alpha U V d w‖ = _
  congr 1
  rw [tsum_eq_sum (s := Icc 1 ⌈x⌉₊) (fun d hd => by
    calc
      _ = ∑' w : ℕ, (0 : ℂ) := tsum_congr (fun w =>
        theorem51TypeIISummand_zero_outside x alpha U V d w hx hU hV (Or.inl hd))
      _ = 0 := tsum_zero)]
  apply sum_congr rfl
  intro d hd
  exact tsum_eq_sum (s := Icc 1 ⌈x⌉₊) (fun w hw =>
    theorem51TypeIISummand_zero_outside x alpha U V d w hx hU hV (Or.inr hw))

end TaoFivePrimes



end


-- Source: examples/five-primes/Theorem51FiniteScaleBridge.lean
section

namespace TaoFivePrimes
open Finset MeasureTheory

noncomputable def theorem51TypeIICoefficient (alpha U V : ℝ) (d w : ℕ) : ℂ :=
  if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
    (ArithmeticFunction.moebius d : ℂ) * (theorem51Centered V w : ℂ) *
      expCircle (alpha * d * w)
  else 0

noncomputable def theorem51FiniteScaleKernel (x alpha U V W : ℝ) : ℂ :=
  ∑ d ∈ Icc 1 ⌈x⌉₊, ∑ w ∈ Icc 1 ⌈x⌉₊,
    theorem51TypeIICoefficient alpha U V d w *
      ((if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧
        W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then W⁻¹ else 0 : ℝ) : ℂ)

lemma theorem51TypeIISummand_factor (x alpha U V : ℝ) (d w : ℕ) :
    theorem51TypeIISummand x alpha U V d w =
      theorem51TypeIICoefficient alpha U V d w * (eta0 ((d : ℝ) * w / x) : ℂ) := by
  unfold theorem51TypeIISummand theorem51TypeIICoefficient
  split_ifs <;> simp

lemma theorem51FiniteScaleKernel_integrable (x alpha U V : ℝ) :
    Integrable (theorem51FiniteScaleKernel x alpha U V) := by
  unfold theorem51FiniteScaleKernel
  apply integrable_finsetSum
  intro d hd
  apply integrable_finsetSum
  intro w hw
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by have := (mem_Icc.mp hd).1; omega)
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by have := (mem_Icc.mp hw).1; omega)
  exact ((scale_pair_integrable x d w hd0 hw0).ofReal).const_mul
    (theorem51TypeIICoefficient alpha U V d w)

lemma theorem51_finite_scale_identity (x alpha U V : ℝ) (hx : 0 < x) :
    (∑ d ∈ Icc 1 ⌈x⌉₊, ∑ w ∈ Icc 1 ⌈x⌉₊, theorem51TypeIISummand x alpha U V d w) =
      4 * ∫ W : ℝ, theorem51FiniteScaleKernel x alpha U V W := by
  let s : Finset ℕ := Icc 1 ⌈x⌉₊
  have hp := finite_eta0_scale_integral (s ×ˢ s) x
    (fun p : ℕ × ℕ => (p.1 : ℝ)) (fun p : ℕ × ℕ => (p.2 : ℝ))
    (fun p => theorem51TypeIICoefficient alpha U V p.1 p.2) hx
    (fun p hp => by
      have hh := (mem_Icc.mp (mem_product.mp hp).1).1
      exact_mod_cast (show 0 < p.1 by omega))
    (fun p hp => by
      have hh := (mem_Icc.mp (mem_product.mp hp).2).1
      exact_mod_cast (show 0 < p.2 by omega))
  simpa only [sum_product, s, theorem51TypeIISummand_factor, theorem51FiniteScaleKernel] using hp

/-- The original public Type II sum now has an exact, integrable scale representation. -/
lemma theorem51TypeII_finite_scale_integral (x alpha U V : ℝ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    theorem51TypeII x alpha U V =
      4 * ‖∫ W : ℝ, theorem51FiniteScaleKernel x alpha U V W‖ := by
  rw [theorem51TypeII_finite x alpha U V hx hU hV,
    theorem51_finite_scale_identity x alpha U V hx, norm_mul]
  norm_num

lemma theorem51TypeII_le_finite_scale_norm (x alpha U V : ℝ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    theorem51TypeII x alpha U V ≤
      4 * ∫ W : ℝ, ‖theorem51FiniteScaleKernel x alpha U V W‖ := by
  rw [theorem51TypeII_finite_scale_integral x alpha U V hx hU hV]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by norm_num)

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51NatOddReindex.lean
section

namespace TaoFivePrimes
open Finset

/-- Positive natural odd intervals agree with the public integer interval interface. -/
lemma nat_odd_interval_sum (A B : ℝ) (N : ℕ) (hA : 0 < A) (hB : B ≤ N)
    (F : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, if A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B ∧ n.Coprime 2 then F n else 0) =
      ∑ w ∈ oddRealInterval A B, F w.toNat := by
  classical
  rw [← sum_filter]
  refine sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    have hh := (mem_filter.mp hn).2
    apply (mem_oddRealInterval A B (n : ℤ)).mpr
    have ho : n % 2 = 1 := Nat.odd_iff.mp (Nat.coprime_two_right.mp hh.2.2)
    exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2.1, by omega⟩
  · intro m hm n hn he
    exact_mod_cast he
  · intro w hw
    have hh := (mem_oddRealInterval A B w).mp hw
    have hw0 : 0 ≤ w := by exact_mod_cast (hA.trans_le hh.1).le
    have he : (w.toNat : ℤ) = w := Int.toNat_of_nonneg hw0
    have her : (w.toNat : ℝ) = (w : ℝ) := by exact_mod_cast he
    refine ⟨w.toNat, ?_, he⟩
    apply mem_filter.mpr
    have hpos : 1 ≤ w.toNat := by
      have hp : (0 : ℝ) < w.toNat := by rw [her]; exact hA.trans_le hh.1
      have hn : 0 < w.toNat := by exact_mod_cast hp
      omega
    have hupper : w.toNat ≤ N := by
      exact_mod_cast (show (w.toNat : ℝ) ≤ N by rw [her]; exact hh.2.1.trans hB)
    refine ⟨mem_Icc.mpr ⟨hpos, hupper⟩, ?_, ?_, ?_⟩
    · rw [her]; exact hh.1
    · rw [her]; exact hh.2.1
    · apply Nat.coprime_two_right.mpr
      apply Nat.odd_iff.mpr
      omega
  · intro n hn
    simp

end TaoFivePrimes


end


-- Source: examples/five-primes/Theorem51ScaleReindex.lean
section

namespace TaoFivePrimes
open Finset

lemma nat_odd_column_sum (A B alpha U w : ℝ) (N : ℕ) (hA : 0 < A) (hB : B ≤ N) :
    (∑ d ∈ Icc 1 N, if A ≤ (d : ℝ) ∧ (d : ℝ) ≤ B ∧ d.Coprime 2 then
      expCircle (alpha * d * w) *
        (if U < (d : ℝ) then (ArithmeticFunction.moebius d : ℂ) else 0) else 0) =
      ∑ n ∈ oddHalfInterval A B,
        expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * scaleColumnCoefficient U n := by
  rw [nat_odd_interval_sum A B N hA hB]
  unfold oddRealInterval
  rw [sum_image (by intro m hm n hn he; change 2 * m + 1 = 2 * n + 1 at he; omega)]
  apply sum_congr rfl
  intro n hn
  have hp : 0 ≤ (2 * n + 1 : ℤ) := by
    have hh := (mem_oddHalfInterval A B n).mp hn
    exact_mod_cast (hA.trans_le hh.1).le
  have he : ((2 * n + 1).toNat : ℝ) = ((2 * n + 1 : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hp)
  simp only [he, scaleColumnCoefficient]

noncomputable def theorem51NatScaleSum (x alpha U V W : ℝ) : ℂ :=
  ∑ w ∈ Icc 1 ⌈x⌉₊, if W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W ∧ w.Coprime 2 then
    (if V < (w : ℝ) then (theorem51Centered V w : ℂ) else 0) *
      (∑ d ∈ Icc 1 ⌈x⌉₊, if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ d.Coprime 2 then
        expCircle (alpha * d * w) *
          (if U < (d : ℝ) then (ArithmeticFunction.moebius d : ℂ) else 0) else 0)
    else 0

lemma theorem51NatScaleSum_eq (x alpha U V W : ℝ)
    (hx : 0 < x) (hW : 1 ≤ W) (hWx : W ≤ x) :
    theorem51NatScaleSum x alpha U V W = theorem51ScaleSum x alpha U V W := by
  have hw : 0 < W := by linarith
  have hcol : x / W ≤ (⌈x⌉₊ : ℝ) := by
    apply le_trans _ (Nat.le_ceil x)
    apply (div_le_iff₀ hw).mpr
    nlinarith
  unfold theorem51NatScaleSum
  rw [nat_odd_interval_sum (W / 2) W ⌈x⌉₊ (by positivity) (hWx.trans (Nat.le_ceil x))]
  unfold theorem51ScaleSum
  apply sum_congr rfl
  intro w hwmem
  have hp : 0 ≤ w := by
    have hh := (mem_oddRealInterval (W / 2) W w).mp hwmem
    exact_mod_cast (show (0 : ℝ) ≤ w by linarith [hh.1])
  have he : (w.toNat : ℝ) = (w : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg hp)
  rw [nat_odd_column_sum (x / (2 * W)) (x / W) alpha U w.toNat ⌈x⌉₊ (by positivity) hcol]
  simp only [he, scaleRowCoefficient]

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51ActualScaleKernel.lean
section

namespace TaoFivePrimes
open Finset MeasureTheory

lemma theorem51FiniteScaleKernel_eq_nat (x alpha U V W : ℝ) :
    theorem51FiniteScaleKernel x alpha U V W =
      theorem51NatScaleSum x alpha U V W * ((W⁻¹ : ℝ) : ℂ) := by
  unfold theorem51FiniteScaleKernel theorem51NatScaleSum
  rw [sum_comm, sum_mul]
  apply sum_congr rfl
  intro w hw
  by_cases hr : W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W ∧ w.Coprime 2
  · rw [if_pos hr, mul_sum, sum_mul]
    apply sum_congr rfl
    intro d hd
    unfold theorem51TypeIICoefficient
    split_ifs <;> simp_all only [Complex.ofReal_zero, mul_zero, zero_mul] <;> first | tauto | ring
  · rw [if_neg hr, zero_mul]
    apply sum_eq_zero
    intro d hd
    unfold theorem51TypeIICoefficient
    split_ifs <;> simp_all only [Complex.ofReal_zero, mul_zero, zero_mul] <;> tauto

/-- Exact connection from the integrable finite kernel to the proved scale sum. -/
lemma theorem51FiniteScaleKernel_eq_scale (x alpha U V W : ℝ)
    (hx : 0 < x) (hW : 1 ≤ W) (hWx : W ≤ x) :
    theorem51FiniteScaleKernel x alpha U V W =
      theorem51ScaleSum x alpha U V W * ((W⁻¹ : ℝ) : ℂ) := by
  rw [theorem51FiniteScaleKernel_eq_nat, theorem51NatScaleSum_eq x alpha U V W hx hW hWx]

lemma theorem51FiniteScaleKernel_norm (x alpha U V W : ℝ)
    (hx : 0 < x) (hW : 1 ≤ W) (hWx : W ≤ x) :
    ‖theorem51FiniteScaleKernel x alpha U V W‖ =
      ‖theorem51ScaleSum x alpha U V W‖ / W := by
  rw [theorem51FiniteScaleKernel_eq_scale x alpha U V W hx hW hWx, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ W⁻¹)]
  rfl

end TaoFivePrimes


end


-- Source: examples/five-primes/Theorem51ScaleIntegralBridge.lean
section

namespace TaoFivePrimes
open Finset MeasureTheory

lemma finite_scale_kernel_zero_of_no_pairs (x alpha U V W : ℝ)
    (h : ∀ d w : ℕ,
      (U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2) →
      (x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W) → False) :
    theorem51FiniteScaleKernel x alpha U V W = 0 := by
  unfold theorem51FiniteScaleKernel
  apply sum_eq_zero
  intro d hd
  apply sum_eq_zero
  intro w hw
  by_cases hg : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
  · have hn := h d w hg
    simp only [theorem51TypeIICoefficient, if_pos hg, if_neg hn, Complex.ofReal_zero, mul_zero]
  · simp only [theorem51TypeIICoefficient, if_neg hg, zero_mul]

lemma finite_scale_kernel_zero_below (x alpha U V W : ℝ) (hWV : W ≤ V) :
    theorem51FiniteScaleKernel x alpha U V W = 0 := by
  apply finite_scale_kernel_zero_of_no_pairs
  intro d w hg hi
  linarith [hg.2.1, hi.2.2.2]

lemma finite_scale_kernel_zero_above (x alpha U V W : ℝ)
    (hU : 0 < U) (hW : 0 < W) (hWU : x / U ≤ W) :
    theorem51FiniteScaleKernel x alpha U V W = 0 := by
  have hx : x / W ≤ U := by
    apply (div_le_iff₀ hW).mpr
    have hh := (div_le_iff₀ hU).mp hWU
    nlinarith
  apply finite_scale_kernel_zero_of_no_pairs
  intro d w hg hi
  linarith [hg.1, hi.2.1]

/-- The actual public Type II sum is bounded by the actual proved scale sum,
integrated over its exact parameter interval. -/
theorem theorem51TypeII_le_scale_integral (x alpha U V : ℝ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : U * V ≤ x) :
    theorem51TypeII x alpha U V ≤
      4 * ∫ W in V..(x / U), ‖theorem51ScaleSum x alpha U V W‖ / W := by
  have hu : 0 < U := by linarith
  have hVU : V ≤ x / U := (le_div_iff₀ hu).mpr (by nlinarith)
  have hUx : x / U ≤ x := (div_le_iff₀ hu).mpr (by nlinarith)
  have he : (∫ W : ℝ, ‖theorem51FiniteScaleKernel x alpha U V W‖) =
      ∫ W in V..(x / U), ‖theorem51ScaleSum x alpha U V W‖ / W := by
    calc
      _ = ∫ W in Set.Icc V (x / U), ‖theorem51FiniteScaleKernel x alpha U V W‖ := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro W hW
        simp only [Set.mem_Icc, not_and_or, not_le] at hW
        rcases hW with hlo | hhi
        · rw [finite_scale_kernel_zero_below x alpha U V W hlo.le, norm_zero]
        · rw [finite_scale_kernel_zero_above x alpha U V W hu
            ((div_pos hx hu).trans hhi) hhi.le, norm_zero]
      _ = ∫ W in Set.Icc V (x / U), ‖theorem51ScaleSum x alpha U V W‖ / W := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro W hW
        exact theorem51FiniteScaleKernel_norm x alpha U V W hx (hV.trans hW.1)
          (hW.2.trans hUx)
      _ = _ := by rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hVU]
  exact (theorem51TypeII_le_finite_scale_norm x alpha U V hx hU hV).trans_eq (congrArg (4 * ·) he)

lemma theorem51_scale_weight_integrable (x alpha U V : ℝ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : U * V ≤ x) :
    IntervalIntegrable (fun W : ℝ => ‖theorem51ScaleSum x alpha U V W‖ / W)
      volume V (x / U) := by
  have hu : 0 < U := by linarith
  have hVU : V ≤ x / U := (le_div_iff₀ hu).mpr (by nlinarith)
  have hUx : x / U ≤ x := (div_le_iff₀ hu).mpr (by nlinarith)
  have hf : IntervalIntegrable (fun W => ‖theorem51FiniteScaleKernel x alpha U V W‖)
      volume V (x / U) := (theorem51FiniteScaleKernel_integrable x alpha U V).norm.intervalIntegrable
  apply hf.congr
  intro W hW
  rw [Set.uIoc_of_le hVU] at hW
  exact theorem51FiniteScaleKernel_norm x alpha U V W hx (hV.trans hW.1.le) (hW.2.trans hUx)

end TaoFivePrimes

end


-- Source: examples/five-primes/Theorem51RootIntegrals.lean
section

namespace TaoFivePrimes
open MeasureTheory

lemma integral_inv_sqrt_positive (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / Real.sqrt t) = 2 * (Real.sqrt b - Real.sqrt a) := by
  have hp : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => 1 / Real.sqrt t) (Set.Icc a b) :=
    continuousOn_const.div Real.continuous_sqrt.continuousOn
      (fun t ht => (Real.sqrt_pos.mpr (hp t ht)).ne')
  have hi : IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt t) volume a b :=
    hc.intervalIntegrable_of_Icc hab
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => 2 * Real.sqrt t) (1 / Real.sqrt t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    convert (Real.hasDerivAt_sqrt (hp t ht).ne').const_mul 2 using 1 <;> first | rfl | ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  convert he using 1 <;> first | rfl | ring

lemma integral_inv_mul_sqrt_positive (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (t * Real.sqrt t)) = 2 / Real.sqrt a - 2 / Real.sqrt b := by
  have hp : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => 1 / (t * Real.sqrt t)) (Set.Icc a b) :=
    continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
      (fun t ht => (mul_pos (hp t ht) (Real.sqrt_pos.mpr (hp t ht))).ne')
  have hi : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.sqrt t)) volume a b :=
    hc.intervalIntegrable_of_Icc hab
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -2 / Real.sqrt t) (1 / (t * Real.sqrt t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 := hp t ht
    have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    convert ((Real.hasDerivAt_sqrt ht0.ne').inv hs0).const_mul (-2) using 1 <;>
      first | rfl | (field_simp; nlinarith [Real.sq_sqrt ht0.le])
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  convert he using 1 <;> first | rfl | ring

lemma integral_log_weight_le (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hn : ∀ t ∈ Set.Icc a b, 0 ≤ f t) :
    (∫ t in a..b, Real.log t * f t) ≤ Real.log b * ∫ t in a..b, f t := by
  have hp : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hl : ContinuousOn Real.log (Set.Icc a b) :=
    continuousOn_id.log (fun t ht => (hp t ht).ne')
  have hi : IntervalIntegrable (fun t => Real.log t * f t) volume a b :=
    (hl.mul hf).intervalIntegrable_of_Icc hab
  have hj : IntervalIntegrable (fun t => Real.log b * f t) volume a b :=
    (continuousOn_const.mul hf).intervalIntegrable_of_Icc hab
  have hm := intervalIntegral.integral_mono_on hab hi hj (fun t ht =>
    mul_le_mul_of_nonneg_right (Real.log_le_log (hp t ht) ht.2) (hn t ht))
  rwa [intervalIntegral.integral_const_mul] at hm

lemma integral_log_inv_sqrt_le (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log t * (1 / Real.sqrt t)) ≤
      2 * Real.sqrt b * Real.log b := by
  have ha0 : 0 < a := by linarith
  have hp : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha0.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => 1 / Real.sqrt t) (Set.Icc a b) :=
    continuousOn_const.div Real.continuous_sqrt.continuousOn
      (fun t ht => (Real.sqrt_pos.mpr (hp t ht)).ne')
  have hm := integral_log_weight_le a b ha0 hab _ hc (fun t ht => by positivity)
  rw [integral_inv_sqrt_positive a b ha0 hab] at hm
  have hl := Real.log_nonneg (ha.trans hab)
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) hl]

lemma integral_log_inv_mul_sqrt_le (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log t * (1 / (t * Real.sqrt t))) ≤
      (2 / Real.sqrt a) * Real.log b := by
  have ha0 : 0 < a := by linarith
  have hp : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha0.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => 1 / (t * Real.sqrt t)) (Set.Icc a b) :=
    continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
      (fun t ht => (mul_pos (hp t ht) (Real.sqrt_pos.mpr (hp t ht))).ne')
  have hm := integral_log_weight_le a b ha0 hab _ hc (fun t ht =>
    div_nonneg (by norm_num) (mul_nonneg (hp t ht).le (Real.sqrt_nonneg t)))
  rw [integral_inv_mul_sqrt_positive a b ha0 hab] at hm
  have hl := Real.log_nonneg (ha.trans hab)
  nlinarith [mul_nonneg (show 0 ≤ 2 / Real.sqrt b by positivity) hl]

end TaoFivePrimes


end


-- Source: examples/five-primes/Theorem51RootNormalization.lean
section

namespace TaoFivePrimes

lemma sqrt_square_div_product (x a b : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    Real.sqrt (x ^ 2 / (a * b)) = x / (Real.sqrt a * Real.sqrt b) := by
  rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx, Real.sqrt_mul ha]

lemma sqrt_two_q_x (x q : ℝ) (hx : 0 < x) (hq : 0 < q) :
    Real.sqrt (2 * q * x) = Real.sqrt 2 * (x / Real.sqrt (x / q)) := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * q),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_div hx.le]
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hsq : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  field_simp
  nlinarith [Real.sq_sqrt hx.le]

lemma sqrt_eight : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
  norm_num

lemma typeII_radical_normalized (x q W : ℝ) (hx : 0 < x) (hq : 0 < q)
    (hW : 0 < W) (hregime : x ≤ q * W) :
    Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) ≤
      (1 / (2 * Real.sqrt 2) * (x / Real.sqrt q) +
        Real.sqrt 2 * (x / Real.sqrt (x / q))) +
      (Real.sqrt x / 2) * Real.sqrt W + (x / Real.sqrt 2) / Real.sqrt W := by
  have h := typeII_radical_unit x q W hx hq hW hregime
  rw [sqrt_square_div_product x 8 q hx.le (by norm_num), sqrt_eight,
    sqrt_square_div_product x 2 W hx.le (by norm_num), sqrt_two_q_x x q hx hq,
    Real.sqrt_div (mul_nonneg hx.le hW.le), Real.sqrt_mul hx.le] at h
  have hfour : Real.sqrt (4 : ℝ) = 2 := by norm_num
  rw [hfour] at h
  convert h using 1 <;> first | rfl | ring

lemma sqrt_scale_endpoint (x U : ℝ) (hx : 0 ≤ x) (hU : 0 < U) :
    Real.sqrt x * Real.sqrt (x / U) = x / Real.sqrt U := by
  rw [Real.sqrt_div hx, ← mul_div_assoc, Real.mul_self_sqrt hx]

end TaoFivePrimes



end


-- Source: examples/five-primes/Theorem51IntegratedMajorant.lean
section

namespace TaoFivePrimes
open MeasureTheory

noncomputable def typeIIIntegralMajorant (A B C t : ℝ) : ℝ :=
  A * (Real.log t / t) + B * (Real.log t * (1 / Real.sqrt t)) +
    C * (Real.log t * (1 / (t * Real.sqrt t)))

lemma typeII_majorant_integrable (a b A B C : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (typeIIIntegralMajorant A B C) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  unfold typeIIIntegralMajorant
  have hp : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht => (ha.trans_le ht.1).ne'
  have hs : ∀ t ∈ Set.Icc a b, Real.sqrt t ≠ 0 :=
    fun t ht => (Real.sqrt_pos.mpr (ha.trans_le ht.1)).ne'
  fun_prop (disch := aesop)

lemma typeII_majorant_integral_bound (a b A B C : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (∫ t in a..b, typeIIIntegralMajorant A B C t) ≤
      (A / 2) * Real.log (b / a) * Real.log (a * b) +
        2 * (B * Real.sqrt b + C / Real.sqrt a) * Real.log b := by
  have ha0 : 0 < a := by linarith
  have hp : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht => (ha0.trans_le ht.1).ne'
  have hs : ∀ t ∈ Set.Icc a b, Real.sqrt t ≠ 0 :=
    fun t ht => (Real.sqrt_pos.mpr (ha0.trans_le ht.1)).ne'
  have h1 : IntervalIntegrable (fun t => A * (Real.log t / t)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    fun_prop (disch := aesop)
  have h2 : IntervalIntegrable (fun t => B * (Real.log t * (1 / Real.sqrt t))) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    fun_prop (disch := aesop)
  have h3 : IntervalIntegrable (fun t => C * (Real.log t * (1 / (t * Real.sqrt t)))) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    fun_prop (disch := aesop)
  unfold typeIIIntegralMajorant
  rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_log_div_factorized a b ha0 hab]
  have hb := mul_le_mul_of_nonneg_left (integral_log_inv_sqrt_le a b ha hab) hB
  have hc := mul_le_mul_of_nonneg_left (integral_log_inv_mul_sqrt_le a b ha hab) hC
  simp only [div_eq_mul_inv] at hb hc ⊢
  nlinarith

lemma typeII_majorant_normalization (A B C W : ℝ) (hW : 0 < W) :
    (A + B * Real.sqrt W + C / Real.sqrt W) * Real.log W / W =
      typeIIIntegralMajorant A B C W := by
  have hs : Real.sqrt W ≠ 0 := (Real.sqrt_pos.mpr hW).ne'
  have he : Real.sqrt W / W = 1 / Real.sqrt W := by
    apply (div_eq_div_iff hW.ne' hs).mpr
    nlinarith [Real.sq_sqrt hW.le]
  calc
    _ = A * (Real.log W / W) + B * (Real.log W * (Real.sqrt W / W)) +
      C * (Real.log W * (1 / (W * Real.sqrt W))) := by ring
    _ = _ := by rw [he]; rfl

end TaoFivePrimes


end


-- Source: examples/five-primes/Theorem51TypeIIIntegration.lean
section

namespace TaoFivePrimes
open MeasureTheory

theorem theorem51_typeII_of_scale_bound
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ)
    (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q) (haunit : a.natAbs = 1)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hUVq : U * V < (q : ℝ) - 1)
    (hscale : ∀ W : ℝ, V ≤ W → W ≤ x / U →
      ‖TaoFivePrimes.theorem51ScaleSum x alpha U V W‖ ≤
        (1.1 / 8) * Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) * Real.log W) :
    TaoFivePrimes.theorem51TypeII x alpha U V ≤
      (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt (x / q))) *
        Real.log (x / (U * V)) * Real.log (V * x / U) +
      (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) *
        Real.log (x / U) := by
  have hu : 0 < U := by linarith
  have hv : 0 < V := by linarith
  have hx : 0 < x := by linarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hU1 : 1 ≤ U := by linarith
  have hV1 : 1 ≤ V := by linarith
  have huv : U * V ≤ x := by linarith
  have hVU : V ≤ x / U := (le_div_iff₀ hu).mpr (by nlinarith)
  let A := 1 / (2 * Real.sqrt 2) * (x / Real.sqrt q) + Real.sqrt 2 * (x / Real.sqrt (x / q))
  let B := Real.sqrt x / 2
  let C := x / Real.sqrt 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (W : ℝ) (hW : W ∈ Set.Icc V (x / U)) :
      ‖theorem51ScaleSum x alpha U V W‖ / W ≤ (1.1 / 8) * typeIIIntegralMajorant A B C W := by
    have hw : 0 < W := hv.trans_le hW.1
    have hl : 0 ≤ Real.log W := Real.log_nonneg (hV1.trans hW.1)
    have hregime := unit_regime_x_le_q_mul_W x U V q W hu.le hv.le hUVq hUV2 hW.1
    have hr := typeII_radical_normalized x q W hx hqr hw hregime
    change Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) ≤
      A + B * Real.sqrt W + C / Real.sqrt W at hr
    calc
      _ ≤ ((1.1 / 8) * Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) * Real.log W) / W :=
        div_le_div_of_nonneg_right (hscale W hW.1 hW.2) hw.le
      _ ≤ ((1.1 / 8) * (A + B * Real.sqrt W + C / Real.sqrt W) * Real.log W) / W := by
        gcongr
      _ = _ := by rw [← typeII_majorant_normalization A B C W hw]; ring
  have hi := theorem51_scale_weight_integrable x alpha U V hx hU1 hV1 huv
  have hj := (typeII_majorant_integrable V (x / U) A B C hv hVU).const_mul (1.1 / 8)
  have hm := intervalIntegral.integral_mono_on hVU hi hj hpoint
  have hint := typeII_majorant_integral_bound V (x / U) A B C hV1 hVU hB hC
  have hbound : theorem51TypeII x alpha U V ≤ (1.1 / 2) *
      ((A / 2) * Real.log ((x / U) / V) * Real.log (V * (x / U)) +
        2 * (B * Real.sqrt (x / U) + C / Real.sqrt V) * Real.log (x / U)) := by
    have hb := theorem51TypeII_le_scale_integral x alpha U V hx hU1 hV1 huv
    rw [intervalIntegral.integral_const_mul] at hm
    have hc := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4)
    have hd := mul_le_mul_of_nonneg_left hint (by norm_num : (0 : ℝ) ≤ 1.1 / 2)
    nlinarith
  have hratio : (x / U) / V = x / (U * V) := by ring
  have hprod : V * (x / U) = V * x / U := by ring
  have hBend : B * Real.sqrt (x / U) = (1 / 2) * (x / Real.sqrt U) := by
    dsimp [B]
    calc
      _ = (Real.sqrt x * Real.sqrt (x / U)) / 2 := by ring
      _ = _ := by rw [sqrt_scale_endpoint x U hx.le hu]; ring
  have hCend : C / Real.sqrt V = (1 / Real.sqrt 2) * (x / Real.sqrt V) := by dsimp [C]; ring
  rw [hratio, hprod, hBend, hCend] at hbound
  have hL1 : 0 ≤ Real.log (x / (U * V)) := Real.log_nonneg ((le_div_iff₀ (mul_pos hu hv)).mpr (by nlinarith))
  have hM : 0 ≤ Real.log (x / U) := Real.log_nonneg (hV1.trans hVU)
  have hL2 : 0 ≤ Real.log (V * x / U) := by
    apply Real.log_nonneg
    rw [← hprod]
    nlinarith
  have hr := typeII_round_constants (x / Real.sqrt q) (x / Real.sqrt (x / q))
    (x / Real.sqrt U) (x / Real.sqrt V)
    (Real.log (x / (U * V)) * Real.log (V * x / U)) (Real.log (x / U))
    (by positivity) (by positivity) (by positivity) (by positivity) (mul_nonneg hL1 hL2) hM
  simp only [← mul_assoc] at hr
  apply le_trans _ hr
  convert hbound using 1 <;> first | rfl | (dsimp [A]; ring)

end TaoFivePrimes



end

#print axioms TaoFivePrimes.vaughan_restricted_centered_identity
#print axioms TaoFivePrimes.weighted_vaughan_centered_split
#print axioms TaoFivePrimes.vaughan_half_log_correction_support
#print axioms TaoFivePrimes.source_typeI_sine_comparison_fails
#print axioms TaoFivePrimes.unit_phase_sine_lower
#print axioms TaoFivePrimes.typeII_radical_unit
#print axioms TaoFivePrimes.typeII_round_constants
#print axioms TaoFivePrimes.unit_typeI_trigonometric_sum_signed
#print axioms TaoFivePrimes.finite_fourier_second_difference_bound
#print axioms TaoFivePrimes.unit_typeI_from_discrete_variation
#print axioms TaoFivePrimes.typeIOddAmplitude_finite
#print axioms TaoFivePrimes.typeI_odd_sum_second_difference_bound
#print axioms TaoFivePrimes.log_product_derivative_hasDerivAt
#print axioms TaoFivePrimes.typeI_curvature_majorant_integral
#print axioms TaoFivePrimes.typeI_curvature_and_jump_budget
#print axioms TaoFivePrimes.typeI_middle_slope_jump
#print axioms TaoFivePrimes.second_difference_from_bounded_variation
#print axioms TaoFivePrimes.joinedSlope_variation_budget
#print axioms TaoFivePrimes.typeI_piecewise_slope_variation
#print axioms TaoFivePrimes.typeI_real_amplitude_continuous
#print axioms TaoFivePrimes.typeI_slope_integral
#print axioms TaoFivePrimes.typeI_actual_discrete_variation
#print axioms TaoFivePrimes.unit_typeI_actual_sum
#print axioms TaoFivePrimes.theorem51_typeI_bound
#print axioms TaoFivePrimes.unit_half_block_spacing
#print axioms TaoFivePrimes.integer_hilbert_eigen_bound
#print axioms TaoFivePrimes.integer_hilbert_sum_bound
#print axioms TaoFivePrimes.bounded_kernel_error
#print axioms TaoFivePrimes.abs_cosecant_sub_inv_le_one
#print axioms TaoFivePrimes.unit_cosecant_block_bound
#print axioms TaoFivePrimes.unit_cosecant_phase_difference
#print axioms TaoFivePrimes.unit_finite_large_sieve
#print axioms TaoFivePrimes.unit_finite_large_sieve_translate
#print axioms TaoFivePrimes.integer_index_card_le
#print axioms TaoFivePrimes.odd_integer_interval_card
#print axioms TaoFivePrimes.unit_bilinear_blocks
#print axioms TaoFivePrimes.typeII_counting_constant
#print axioms TaoFivePrimes.unit_odd_rectangle
#print axioms TaoFivePrimes.theorem51Centered_energy
#print axioms TaoFivePrimes.moebius_coefficient_energy
#print axioms TaoFivePrimes.integer_interval_blocks_energy
#print axioms TaoFivePrimes.integer_block_count
#print axioms TaoFivePrimes.unit_padded_odd_rectangle
#print axioms TaoFivePrimes.scale_column_block_count
#print axioms TaoFivePrimes.scale_row_energy
#print axioms TaoFivePrimes.theorem51_scale_bound_positive
#print axioms TaoFivePrimes.theorem51_scale_bound_signed
#print axioms TaoFivePrimes.integral_log_div_factorized
#print axioms TaoFivePrimes.theorem51ScaleSum_zero_below
#print axioms TaoFivePrimes.theorem51ScaleSum_zero_above
#print axioms TaoFivePrimes.eta0_pair_scale_integral
#print axioms TaoFivePrimes.scale_pair_integrable
#print axioms TaoFivePrimes.finite_eta0_scale_integral
#print axioms TaoFivePrimes.theorem51TypeII_finite
#print axioms TaoFivePrimes.theorem51TypeII_finite_scale_integral
#print axioms TaoFivePrimes.theorem51NatScaleSum_eq
#print axioms TaoFivePrimes.theorem51TypeII_le_scale_integral
#print axioms TaoFivePrimes.theorem51_scale_weight_integrable
#print axioms TaoFivePrimes.integral_log_inv_sqrt_le
#print axioms TaoFivePrimes.integral_log_inv_mul_sqrt_le
#print axioms TaoFivePrimes.typeII_radical_normalized
#print axioms TaoFivePrimes.typeII_majorant_integral_bound
#print axioms TaoFivePrimes.theorem51_typeII_of_scale_bound