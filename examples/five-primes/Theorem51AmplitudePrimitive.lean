import examples.«five-primes».Theorem51SlopeVariation

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
