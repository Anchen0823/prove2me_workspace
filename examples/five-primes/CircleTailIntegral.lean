import examples.«five-primes».CircleTail

open MeasureTheory

namespace TaoFivePrimes

theorem circle_tail_integral_bound (F : C(AddCircle (1 : ℝ), ℝ))
    (B r : ℝ) (hB : 0 ≤ B) (hr : 0 < r) (hrhi : r ≤ 1 / 2)
    (hbound : ∀ t : ℝ, 0 < |t| → |t| ≤ 1 / 2 →
      F (t : AddCircle (1 : ℝ)) ≤ B * t ^ (-2 : ℤ)) :
    (∫ α in {α : AddCircle (1 : ℝ) | r < ‖α‖}, F α
      ∂AddCircle.haarAddCircle) ≤ 2 * B / r := by
  classical
  let E : Set (AddCircle (1 : ℝ)) := {α | r < ‖α‖}
  let f : ℝ → ℝ := fun t => F (t : AddCircle (1 : ℝ))
  let A : Set ℝ := (fun t : ℝ => (t : AddCircle (1 : ℝ))) ⁻¹' E
  let g : ℝ → ℝ := A.indicator f
  have hE : MeasurableSet E := isOpen_lt continuous_const continuous_norm |>.measurableSet
  have hA : MeasurableSet A := hE.preimage (AddCircle.continuous_mk' (1 : ℝ)).measurable
  have hf : Continuous f := F.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hg (a b : ℝ) : IntervalIntegrable g volume a b :=
    ⟨(hf.intervalIntegrable a b).1.indicator hA, (hf.intervalIntegrable a b).2.indicator hA⟩
  have hnorm (t : ℝ) (ht : |t| ≤ 1 / 2) : ‖(t : AddCircle (1 : ℝ))‖ = |t| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 (by simpa using ht)
  have hcenter : (∫ t in (-r)..r, g t) = 0 := by
    calc
      _ = ∫ t in (-r)..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [Set.uIcc_of_le (by linarith)] at ht
        have htabs : |t| ≤ r := abs_le.mpr ⟨ht.1, ht.2⟩
        have hn : t ∉ A := by
          change ¬ r < ‖(t : AddCircle (1 : ℝ))‖
          rw [hnorm t (htabs.trans hrhi)]
          exact not_lt.mpr htabs
        exact Set.indicator_of_notMem hn f
      _ = 0 := by simp
  have hleft : (∫ t in (-(1 / 2 : ℝ))..(-r), g t) =
      ∫ t in (-(1 / 2 : ℝ))..(-r), f t := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro t ht
    have htneg : t < 0 := by linarith [ht.2]
    have htabs : |t| ≤ 1 / 2 := by rw [abs_of_neg htneg]; linarith [ht.1]
    have hm : t ∈ A := by
      change r < ‖(t : AddCircle (1 : ℝ))‖
      rw [hnorm t htabs, abs_of_neg htneg]
      linarith [ht.2]
    exact Set.indicator_of_mem hm f
  have hright : (∫ t in r..(1 / 2 : ℝ), g t) =
      ∫ t in r..(1 / 2 : ℝ), f t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hrhi
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have htabs : |t| ≤ 1 / 2 := by rw [abs_of_pos htpos]; exact ht.2.le
    have hm : t ∈ A := by
      change r < ‖(t : AddCircle (1 : ℝ))‖
      rw [hnorm t htabs, abs_of_pos htpos]
      exact ht.1
    exact Set.indicator_of_mem hm f
  have hhaar : (∫ α in E, F α ∂AddCircle.haarAddCircle) =
      ∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), g t := by
    rw [← MeasureTheory.integral_indicator hE, AddCircle.integral_haarAddCircle]
    simp only [inv_one, one_smul]
    rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) (-(1 / 2 : ℝ)) (E.indicator F)]
    norm_num only
    rfl
  have hp : (∫ t in r..(1 / 2 : ℝ), f t) ≤ B / r := by
    apply positive_tail_integral_bound f hf B r hB hr hrhi
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    exact hbound t (abs_pos.mpr htpos.ne') (by rw [abs_of_pos htpos]; exact ht.2)
  have hn : (∫ t in (-(1 / 2 : ℝ))..(-r), f t) ≤ B / r := by
    apply negative_tail_integral_bound f hf B r hB hr hrhi
    intro t ht
    have htneg : t < 0 := by linarith [ht.2]
    exact hbound t (abs_pos.mpr htneg.ne) (by rw [abs_of_neg htneg]; linarith [ht.1])
  change (∫ α in E, F α ∂AddCircle.haarAddCircle) ≤ _
  rw [hhaar, ← intervalIntegral.integral_add_adjacent_intervals
    (hg (-(1 / 2)) (-r)) (hg (-r) (1 / 2)),
    ← intervalIntegral.integral_add_adjacent_intervals (hg (-r) r) (hg r (1 / 2)),
    hleft, hcenter, hright]
  rw [mul_div_assoc]
  linarith

theorem cutoff_circle_tail_integral_bound (x : ℕ) (hx : 10 ≤ x)
    (r : ℝ) (hr : 0 < r) (hrhi : r ≤ 1 / 2) :
    (∫ α in {α : AddCircle (1 : ℝ) | r < ‖α‖},
      ‖TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α‖
        ∂AddCircle.haarAddCircle) ≤ 5 / ((x : ℝ) * r) := by
  let F : C(AddCircle (1 : ℝ), ℝ) :=
    ⟨fun α => ‖TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
      (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α‖,
      (TaoFourierIdentity.continuous_fourierPolynomial _ _ _).norm⟩
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have h := circle_tail_integral_bound F (5 / (2 * (x : ℝ))) r
    (by positivity) hr hrhi (by
      intro t ht ht'
      have hdec := cutoff_fourier_real_decay x hx t ht' (abs_pos.mp ht)
      have heq : 5 / (2 * (x : ℝ) * t ^ 2) = (5 / (2 * (x : ℝ))) * t ^ (-2 : ℤ) := by
        simp [zpow_neg, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      change _ ≤ _
      rw [← heq]
      exact hdec)
  have heq : 2 * (5 / (2 * (x : ℝ))) / r = 5 / ((x : ℝ) * r) := by
    field_simp
  rw [heq] at h
  exact h

end TaoFivePrimes
