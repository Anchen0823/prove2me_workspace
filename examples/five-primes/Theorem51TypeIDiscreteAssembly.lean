import examples.«five-primes».Theorem51TypeITrig
import examples.«five-primes».Theorem51DiscreteSecondDifference

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
