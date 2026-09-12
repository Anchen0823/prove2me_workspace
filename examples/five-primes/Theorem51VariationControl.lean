import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

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
