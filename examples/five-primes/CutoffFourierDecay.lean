import examples.«five-primes».CutoffDifferences
import examples.«five-primes».FiniteDifference
import examples.«five-primes».FourierMoments

open scoped BigOperators

namespace TaoFiniteDifference

theorem shift_apply (a : ℤ →₀ ℂ) (n : ℤ) : shift a n = a (n - 1) := by
  have h := Finsupp.mapDomain_apply (f := fun k : ℤ => k + 1)
    (by intro i j hij; exact add_right_cancel hij) a (n - 1)
  simpa [shift] using h

theorem difference_apply (a : ℤ →₀ ℂ) (n : ℤ) :
    difference a n = a n - a (n - 1) := by
  simp [difference, shift_apply]

theorem second_difference_apply (a : ℤ →₀ ℂ) (n : ℤ) :
    difference (difference a) n = a n - 2 * a (n - 1) + a (n - 2) := by
  rw [difference_apply, difference_apply, difference_apply]
  rw [show n - 1 - 1 = n - 2 by omega]
  ring

end TaoFiniteDifference

namespace TaoFivePrimes

private theorem norm_real_second_difference (a b c : ℝ) :
    ‖(a : ℂ) - 2 * (b : ℂ) + (c : ℂ)‖ = |a - 2 * b + c| := by
  have h : (a : ℂ) - 2 * (b : ℂ) + (c : ℂ) = ((a - 2 * b + c : ℝ) : ℂ) := by
    push_cast
    <;> ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]

theorem eta1_zero_of_nonpos (t : ℝ) (ht : t ≤ 0) : eta1 t = 0 := by
  rw [eta1_left t (by linarith), max_eq_left (by linarith)]

theorem eta1_zero_of_one_le (t : ℝ) (ht : 1 ≤ t) : eta1 t = 0 := by
  rw [eta1_right t (by linarith), max_eq_left (by linarith)]

theorem eta1_nonzero_interval (t : ℝ) (ht : eta1 t ≠ 0) : 0 < t ∧ t < 1 := by
  constructor
  · by_contra h
    exact ht (eta1_zero_of_nonpos t (by linarith))
  · by_contra h
    exact ht (eta1_zero_of_one_le t (by linarith))

theorem sampled_cutoff_support (x : ℕ) (hx : 0 < x) (n : ℤ)
    (hn : (eta1 ((n : ℝ) / x) : ℂ) ≠ 0) :
    n ∈ (Finset.range (x + 1)).image (fun k : ℕ => (k : ℤ)) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have ht := eta1_nonzero_interval ((n : ℝ) / x) (by exact_mod_cast hn)
  have hlo : (0 : ℝ) < n := by
    have h := (lt_div_iff₀ hxR).mp ht.1
    linarith
  have hhi : (n : ℝ) < x := by
    have h := (div_lt_iff₀ hxR).mp ht.2
    linarith
  have hn0 : 0 ≤ n := by exact_mod_cast (le_of_lt hlo)
  have hnx : n < x := by exact_mod_cast hhi
  apply Finset.mem_image.mpr
  refine ⟨n.toNat, ?_, ?_⟩
  · simp only [Finset.mem_range]
    omega
  · omega

noncomputable def sampledCutoff (x : ℕ) (hx : 0 < x) : ℤ →₀ ℂ :=
  Finsupp.onFinset ((Finset.range (x + 1)).image (fun k : ℕ => (k : ℤ)))
    (fun n => (eta1 ((n : ℝ) / x) : ℂ)) (sampled_cutoff_support x hx)

@[simp] theorem sampledCutoff_apply (x : ℕ) (hx : 0 < x) (n : ℤ) :
    sampledCutoff x hx n = (eta1 ((n : ℝ) / x) : ℂ) := rfl

theorem sampledCutoff_transform (x : ℕ) (hx : 0 < x) (α : AddCircle (1 : ℝ)) :
    TaoFiniteDifference.transform (sampledCutoff x hx) α =
      TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α := by
  classical
  unfold TaoFiniteDifference.transform sampledCutoff
  rw [Finsupp.sum_onFinset _ _ _ _ (by intros; simp)]
  rw [Finset.sum_image]
  · simp [TaoFourierIdentity.fourierPolynomial]
  · intro i hi j hj hij
    change (i : ℤ) = (j : ℤ) at hij
    exact_mod_cast hij

theorem sampledCutoff_zero_left (x : ℕ) (hx : 10 ≤ x) (n : ℤ) (hn : n ≤ 1) :
    sampledCutoff x (by omega) n = 0 := by
  have hxR : (10 : ℝ) ≤ x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hnR : (n : ℝ) ≤ 1 := by exact_mod_cast hn
  have ht : (n : ℝ) / x ≤ 1 / 10 := by
    apply (div_le_iff₀ hxpos).2
    linarith
  rw [sampledCutoff_apply, eta1_left _ (by linarith), max_eq_left (by linarith)]
  simp

theorem sampledCutoff_zero_right (x : ℕ) (hx : 0 < x) (n : ℤ) (hn : (x : ℤ) ≤ n) :
    sampledCutoff x hx n = 0 := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hnR : (x : ℝ) ≤ n := by exact_mod_cast hn
  rw [sampledCutoff_apply, eta1_zero_of_one_le _ ((le_div_iff₀ hxpos).2 (by linarith))]
  simp

theorem sampledCutoff_second_difference_support (x : ℕ) (hx : 10 ≤ x) :
    (TaoFiniteDifference.difference (TaoFiniteDifference.difference
      (sampledCutoff x (by omega)))).support ⊆
        (Finset.range x).image (fun n : ℕ => (n : ℤ) + 2) := by
  intro n hn
  rw [Finsupp.mem_support_iff] at hn
  have hlo : 2 ≤ n := by
    by_contra h
    apply hn
    rw [TaoFiniteDifference.second_difference_apply,
      sampledCutoff_zero_left x hx n (by omega),
      sampledCutoff_zero_left x hx (n - 1) (by omega),
      sampledCutoff_zero_left x hx (n - 2) (by omega)]
    ring
  have hhi : n < (x : ℤ) + 2 := by
    by_contra h
    apply hn
    rw [TaoFiniteDifference.second_difference_apply,
      sampledCutoff_zero_right x (by omega) n (by omega),
      sampledCutoff_zero_right x (by omega) (n - 1) (by omega),
      sampledCutoff_zero_right x (by omega) (n - 2) (by omega)]
    ring
  apply Finset.mem_image.mpr
  refine ⟨(n - 2).toNat, ?_, ?_⟩
  · simp only [Finset.mem_range]
    omega
  · omega

theorem sampledCutoff_second_difference_mass (x : ℕ) (hx : 10 ≤ x) :
    (∑ n ∈ (TaoFiniteDifference.difference (TaoFiniteDifference.difference
      (sampledCutoff x (by omega)))).support,
      ‖TaoFiniteDifference.difference (TaoFiniteDifference.difference
        (sampledCutoff x (by omega))) n‖) ≤ 40 / (x : ℝ) := by
  classical
  let d := TaoFiniteDifference.difference (TaoFiniteDifference.difference
    (sampledCutoff x (by omega)))
  change (∑ n ∈ d.support, ‖d n‖) ≤ _
  calc
    _ = ∑ n ∈ (Finset.range x).image (fun n : ℕ => (n : ℤ) + 2), ‖d n‖ := by
      apply Finset.sum_subset (sampledCutoff_second_difference_support x hx)
      intro n hn hnot
      rw [Finsupp.notMem_support_iff.mp hnot, norm_zero]
    _ = ∑ n ∈ Finset.range x, ‖d ((n : ℤ) + 2)‖ := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      change (i : ℤ) + 2 = (j : ℤ) + 2 at hij
      omega
    _ = ∑ n ∈ Finset.range x,
        |eta1 (((n : ℝ) + 2) / x) - 2 * eta1 (((n : ℝ) + 1) / x) +
          eta1 ((n : ℝ) / x)| := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [d]
      rw [TaoFiniteDifference.second_difference_apply]
      rw [show (n : ℤ) + 2 - 1 = (n : ℤ) + 1 by omega]
      simp only [sampledCutoff_apply]
      norm_num only [Int.cast_add, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
        add_sub_cancel_right]
      exact norm_real_second_difference _ _ _
    _ ≤ _ := eta1_second_difference_mass x hx

theorem cutoff_fourier_decay (x : ℕ) (hx : 10 ≤ x) (α : AddCircle (1 : ℝ)) :
    ‖1 - fourier 1 α‖ ^ 2 *
      ‖TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α‖ ≤ 40 / (x : ℝ) := by
  have h := TaoFiniteDifference.second_difference_decay (sampledCutoff x (by omega)) α
  rw [sampledCutoff_transform] at h
  exact h.trans (sampledCutoff_second_difference_mass x hx)

end TaoFivePrimes
