import examples.«five-primes».CutoffFourierDecay

open MeasureTheory

namespace TaoFivePrimes

theorem norm_one_sub_fourier_coe (t : ℝ) :
    ‖1 - fourier 1 (t : AddCircle (1 : ℝ))‖ = 2 * |Real.sin (Real.pi * t)| := by
  have he : fourier 1 (t : AddCircle (1 : ℝ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    <;> ring
  rw [he, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * t) / 2 = Real.pi * t by ring]
  simp [norm_mul, Real.norm_eq_abs]

theorem fourier_chord_lower_bound (t : ℝ) (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖1 - fourier 1 (t : AddCircle (1 : ℝ))‖ := by
  have harg : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hc : (2 / Real.pi) * (Real.pi * |t|) = 2 * |t| := by
    field_simp
  rw [hc] at hs
  rw [norm_one_sub_fourier_coe]
  linarith

theorem cutoff_fourier_real_decay (x : ℕ) (hx : 10 ≤ x) (t : ℝ)
    (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    ‖TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ))
        (t : AddCircle (1 : ℝ))‖ ≤ 5 / (2 * (x : ℝ) * t ^ 2) := by
  let F := TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
    (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) (t : AddCircle (1 : ℝ))
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have htpos : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
  have h := cutoff_fourier_decay x hx (t : AddCircle (1 : ℝ))
  change ‖1 - fourier 1 (t : AddCircle (1 : ℝ))‖ ^ 2 * ‖F‖ ≤ 40 / (x : ℝ) at h
  have hs : (4 * |t|) ^ 2 ≤ ‖1 - fourier 1 (t : AddCircle (1 : ℝ))‖ ^ 2 := by
    gcongr
    exact fourier_chord_lower_bound t ht
  have hp := mul_le_mul_of_nonneg_right hs (norm_nonneg F)
  have hprod : 16 * t ^ 2 * ‖F‖ ≤ 40 / (x : ℝ) := by
    have heq : (4 * |t|) ^ 2 = 16 * t ^ 2 := by rw [mul_pow, sq_abs]; norm_num
    rw [heq] at hp
    exact hp.trans h
  have hscaled := (le_div_iff₀ hxpos).mp hprod
  change ‖F‖ ≤ _
  apply (le_div_iff₀ (show 0 < 2 * (x : ℝ) * t ^ 2 by positivity)).2
  nlinarith

theorem integral_inverse_square (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) :
    (∫ t in r..s, t ^ (-2 : ℤ)) = r⁻¹ - s⁻¹ := by
  rw [integral_zpow (Or.inr ⟨by norm_num, ?_⟩)]
  · norm_num
    ring
  · rw [Set.uIcc_of_le hrs]
    intro h
    exact (not_le_of_gt hr) h.1

theorem positive_tail_integral_bound (f : ℝ → ℝ) (hf : Continuous f)
    (B r : ℝ) (hB : 0 ≤ B) (hr : 0 < r) (hrhi : r ≤ 1 / 2)
    (hbound : ∀ t ∈ Set.Icc r (1 / 2), f t ≤ B * t ^ (-2 : ℤ)) :
    (∫ t in r..(1 / 2 : ℝ), f t) ≤ B / r := by
  have hzero : (0 : ℝ) ∉ Set.uIcc r (1 / 2) := by
    rw [Set.uIcc_of_le hrhi]
    intro h
    exact (not_le_of_gt hr) h.1
  have hg : IntervalIntegrable (fun t : ℝ => B * t ^ (-2 : ℤ)) volume r (1 / 2) :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)).const_mul B
  calc
    _ ≤ ∫ t in r..(1 / 2 : ℝ), B * t ^ (-2 : ℤ) :=
      intervalIntegral.integral_mono_on hrhi (hf.intervalIntegrable _ _) hg hbound
    _ = B * (r⁻¹ - 2) := by
      rw [intervalIntegral.integral_const_mul, integral_inverse_square r (1 / 2) hr hrhi]
      norm_num
    _ ≤ B / r := by rw [div_eq_mul_inv]; nlinarith

theorem negative_tail_integral_bound (f : ℝ → ℝ) (hf : Continuous f)
    (B r : ℝ) (hB : 0 ≤ B) (hr : 0 < r) (hrhi : r ≤ 1 / 2)
    (hbound : ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (-r), f t ≤ B * t ^ (-2 : ℤ)) :
    (∫ t in (-(1 / 2 : ℝ))..(-r), f t) ≤ B / r := by
  have h := positive_tail_integral_bound (fun t => f (-t)) (hf.comp continuous_neg)
    B r hB hr hrhi (by
      intro t ht
      have hb := hbound (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simpa using hb)
  rw [intervalIntegral.integral_comp_neg] at h
  exact h

end TaoFivePrimes
