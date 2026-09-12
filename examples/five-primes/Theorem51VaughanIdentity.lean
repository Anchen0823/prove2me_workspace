import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

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
