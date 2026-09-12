import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.FiniteSupport.Basic

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
