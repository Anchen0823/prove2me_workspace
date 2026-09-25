namespace TaoFivePrimes
open Finset MeasureTheory

/-! ## Glue for `theorem51_typeII_dyadic_representation`

The platform's dyadic block is the double `tsum` with the coefficient guard and the
dyadic indicator *merged* into one `if`.  We split them, relate the block to the
local `theorem51FiniteScaleKernel` (which carries the extra factor `W⁻¹`), and
transfer the support / integrability / integral statements proved locally for the
scale sum. -/

/-- The platform block with the coefficient and the indicator split apart. -/
noncomputable def theorem51DyadicBlock (x alpha U V W : ℝ) : ℂ :=
  ∑' d : ℕ, ∑' w : ℕ, theorem51TypeIICoefficient alpha U V d w *
    ((if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
      then (1 : ℝ) else 0 : ℝ) : ℂ)

/-- Pointwise: the platform summand (one conjunction) equals the split form. -/
lemma theorem51DyadicSummand_eq (x alpha U V W : ℝ) (d w : ℕ) :
    (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 ∧
        x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
      ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((theorem51Centered V w : ℝ) : ℂ) *
        expCircle (alpha * d * w)
    else 0) =
      theorem51TypeIICoefficient alpha U V d w *
        ((if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
          then (1 : ℝ) else 0 : ℝ) : ℂ) := by
  unfold theorem51TypeIICoefficient
  by_cases h1 : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
  · by_cases h2 : x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
    · rw [if_pos (by tauto), if_pos h1, if_pos h2]
      simp
    · rw [if_neg (by tauto), if_pos h1, if_neg h2]
      simp
  · rw [if_neg (by tauto), if_neg h1]
    simp

/-- The block written with the platform's single-conjunction summand. -/
lemma theorem51DyadicBlock_eq_tsum (x alpha U V W : ℝ) :
    theorem51DyadicBlock x alpha U V W =
      ∑' d : ℕ, ∑' w : ℕ, (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 ∧
          x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((theorem51Centered V w : ℝ) : ℂ) *
          expCircle (alpha * d * w) else 0) := by
  unfold theorem51DyadicBlock
  apply tsum_congr
  intro d
  apply tsum_congr
  intro w
  exact (theorem51DyadicSummand_eq x alpha U V W d w).symm

/-- On the dyadic guard, both indices lie in `[1, ⌈x⌉₊]`. -/
lemma theorem51DyadicGuard_mem (x U V W : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hx : 0 < x) (hW1 : 1 ≤ W) (hWx : W ≤ x) (d w : ℕ)
    (h : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 ∧
      x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W) :
    d ∈ Icc 1 ⌈x⌉₊ ∧ w ∈ Icc 1 ⌈x⌉₊ := by
  have hWpos : 0 < W := lt_of_lt_of_le (by norm_num) hW1
  have hd1 : 1 ≤ d := by
    have : (1 : ℝ) < (d : ℝ) := lt_of_le_of_lt hU h.1
    exact_mod_cast (show (1 : ℝ) ≤ (d : ℝ) from this.le)
  have hw1 : 1 ≤ w := by
    have : (1 : ℝ) < (w : ℝ) := lt_of_le_of_lt hV h.2.1
    exact_mod_cast (show (1 : ℝ) ≤ (w : ℝ) from this.le)
  have hdx : (d : ℝ) ≤ x := by
    have h1 : x / W ≤ x := (div_le_iff₀ hWpos).mpr (by nlinarith)
    exact h.2.2.2.2.2.1.trans h1
  have hwx : (w : ℝ) ≤ x := h.2.2.2.2.2.2.2.trans hWx
  refine ⟨mem_Icc.mpr ⟨hd1, ?_⟩, mem_Icc.mpr ⟨hw1, ?_⟩⟩
  · exact_mod_cast le_trans hdx (Nat.le_ceil x)
  · exact_mod_cast le_trans hwx (Nat.le_ceil x)

/-- The block term vanishes outside the finite rectangle. -/
lemma theorem51DyadicTerm_zero_outside (x alpha U V W : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hx : 0 < x) (hW1 : 1 ≤ W) (hWx : W ≤ x) (d w : ℕ)
    (hout : d ∉ Icc 1 ⌈x⌉₊ ∨ w ∉ Icc 1 ⌈x⌉₊) :
    theorem51TypeIICoefficient alpha U V d w *
      ((if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
        then (1 : ℝ) else 0 : ℝ) : ℂ) = 0 := by
  by_cases hind : x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
  · rw [if_pos hind]
    have hcoeff : theorem51TypeIICoefficient alpha U V d w = 0 := by
      unfold theorem51TypeIICoefficient
      by_cases hg : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
      · exfalso
        have hmem := theorem51DyadicGuard_mem x U V W hU hV hx hW1 hWx d w
          ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, hind.1, hind.2.1, hind.2.2.1, hind.2.2.2⟩
        rcases hout with h | h
        · exact h hmem.1
        · exact h hmem.2
      · rw [if_neg hg]
    rw [hcoeff, zero_mul]
  · rw [if_neg hind, Complex.ofReal_zero, mul_zero]

/-- The block is the finite rectangle sum over `[1, ⌈x⌉₊]²`. -/
lemma theorem51DyadicBlock_eq_finset (x alpha U V W : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hx : 0 < x) (hW1 : 1 ≤ W) (hWx : W ≤ x) :
    theorem51DyadicBlock x alpha U V W =
      ∑ d ∈ Icc 1 ⌈x⌉₊, ∑ w ∈ Icc 1 ⌈x⌉₊, theorem51TypeIICoefficient alpha U V d w *
        ((if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
          then (1 : ℝ) else 0 : ℝ) : ℂ) := by
  unfold theorem51DyadicBlock
  rw [tsum_eq_sum (s := Icc 1 ⌈x⌉₊) (fun d hd => by
    calc _ = ∑' w : ℕ, (0 : ℂ) := tsum_congr (fun w =>
          theorem51DyadicTerm_zero_outside x alpha U V W hU hV hx hW1 hWx d w (Or.inl hd))
      _ = 0 := tsum_zero)]
  apply sum_congr rfl
  intro d hd
  rw [tsum_eq_sum (s := Icc 1 ⌈x⌉₊) (fun w hw =>
    theorem51DyadicTerm_zero_outside x alpha U V W hU hV hx hW1 hWx d w (Or.inr hw))]

/-- The rectangle sum times `W⁻¹` is the local kernel (which carries the `W⁻¹`). -/
lemma theorem51DyadicRect_mul_inv_eq_kernel (x alpha U V W : ℝ) :
    ((∑ d ∈ Icc 1 ⌈x⌉₊, ∑ w ∈ Icc 1 ⌈x⌉₊, theorem51TypeIICoefficient alpha U V d w *
        ((if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
          then (1 : ℝ) else 0 : ℝ) : ℂ)) * ((W⁻¹ : ℝ) : ℂ))
      = theorem51FiniteScaleKernel x alpha U V W := by
  unfold theorem51FiniteScaleKernel
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro d hd
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro w hw
  by_cases hind : x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
  · rw [if_pos hind, if_pos hind, Complex.ofReal_one, mul_one]
  · rw [if_neg hind, if_neg hind, Complex.ofReal_zero, mul_zero, zero_mul]

/-- The block is the local kernel times `W`. -/
lemma theorem51DyadicBlock_eq_kernel_mul (x alpha U V W : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hx : 0 < x) (hW1 : 1 ≤ W) (hWx : W ≤ x) :
    theorem51DyadicBlock x alpha U V W = theorem51FiniteScaleKernel x alpha U V W * (W : ℂ) := by
  have hW0 : (W : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hW1)
  have h := theorem51DyadicRect_mul_inv_eq_kernel x alpha U V W
  have h2 := congrArg (fun z : ℂ => z * (W : ℂ)) h
  rw [mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hW0, Complex.ofReal_one, mul_one] at h2
  rw [theorem51DyadicBlock_eq_finset x alpha U V W hU hV hx hW1 hWx]
  exact h2

/-- The kernel vanishes for `W < 1`. -/
lemma theorem51FiniteScaleKernel_zero_small (x alpha U V W : ℝ) (hW : W < 1) :
    theorem51FiniteScaleKernel x alpha U V W = 0 := by
  unfold theorem51FiniteScaleKernel
  apply sum_eq_zero
  intro d hd
  apply sum_eq_zero
  intro w hw
  have hw1 : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast (mem_Icc.mp hw).1
  have hbad : ¬ (x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W) := by
    intro h
    linarith [h.2.2.2]
  rw [if_neg hbad, Complex.ofReal_zero, mul_zero]

/-- The kernel vanishes for `W > x`. -/
lemma theorem51FiniteScaleKernel_zero_gt_x (x alpha U V W : ℝ) (hx : 0 < x) (hWx : x < W) :
    theorem51FiniteScaleKernel x alpha U V W = 0 := by
  unfold theorem51FiniteScaleKernel
  apply sum_eq_zero
  intro d hd
  apply sum_eq_zero
  intro w hw
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
  have hbad : ¬ (x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W) := by
    intro h
    have hWpos : 0 < W := lt_trans hx hWx
    have h1 : x / W < 1 := (div_lt_one hWpos).mpr hWx
    linarith [h.2.1]
  rw [if_neg hbad, Complex.ofReal_zero, mul_zero]

/-- The block vanishes for `W < 1` (hence also for `W ≤ 0`). -/
lemma theorem51DyadicBlock_zero_small (x alpha U V W : ℝ) (hW : W < 1) :
    theorem51DyadicBlock x alpha U V W = 0 := by
  unfold theorem51DyadicBlock
  have hzero : ∀ d w : ℕ, theorem51TypeIICoefficient alpha U V d w *
      ((if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
        then (1 : ℝ) else 0 : ℝ) : ℂ) = 0 := by
    intro d w
    by_cases hind : x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
    · rw [if_pos hind]
      have hwlt : ((w : ℝ)) < 1 := lt_of_le_of_lt hind.2.2.2 hW
      have hw0 : w = 0 := by
        have : (w : ℕ) < 1 := by exact_mod_cast hwlt
        omega
      subst hw0
      simp [theorem51TypeIICoefficient, Nat.coprime_zero_left]
    · rw [if_neg hind, Complex.ofReal_zero, mul_zero]
  rw [tsum_congr (fun d => tsum_congr (fun w => hzero d w))]
  simp

/-- The block vanishes off `[V, x/U]`. -/
lemma theorem51DyadicBlock_zero_outside (x alpha U V W : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hx : 0 < x) (hUx : U < x) (hVx : V < x) (hUV : U * V ≤ x)
    (hW : W ∉ Set.Icc V (x / U)) : theorem51DyadicBlock x alpha U V W = 0 := by
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  simp only [Set.mem_Icc, not_and_or, not_le] at hW
  rcases hW with hlt | hgt
  · by_cases h1 : W < 1
    · exact theorem51DyadicBlock_zero_small x alpha U V W h1
    · have hW1 : 1 ≤ W := le_of_not_gt h1
      have hWx : W ≤ x := by linarith
      rw [theorem51DyadicBlock_eq_kernel_mul x alpha U V W hU hV hx hW1 hWx,
        finite_scale_kernel_zero_below x alpha U V W hlt.le, zero_mul]
  · have hWpos : 0 < W := by
      have : 0 < x / U := div_pos hx hUpos
      linarith
    have hxW : x / W < U := by
      rw [div_lt_iff₀ hWpos]
      exact ((div_lt_iff₀ hUpos).mp hgt).trans_eq (mul_comm W U)
    unfold theorem51DyadicBlock
    have hzero : ∀ d w : ℕ, theorem51TypeIICoefficient alpha U V d w *
        ((if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
          then (1 : ℝ) else 0 : ℝ) : ℂ) = 0 := by
      intro d w
      by_cases hind : x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
      · rw [if_pos hind]
        have hcoeff : theorem51TypeIICoefficient alpha U V d w = 0 := by
          unfold theorem51TypeIICoefficient
          by_cases hg : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
          · exfalso
            linarith [hg.1, hind.2.1]
          · rw [if_neg hg]
        rw [hcoeff, zero_mul]
      · rw [if_neg hind, Complex.ofReal_zero, mul_zero]
    rw [tsum_congr (fun d => tsum_congr (fun w => hzero d w))]
    simp

/-- Integrability of the platform integrand on `(0, ∞)`. -/
lemma theorem51DyadicBlock_integrableOn (x alpha U V : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hx : 0 < x) (hUx : U < x) (hVx : V < x) (hUV : U * V ≤ x) :
    IntegrableOn (fun W : ℝ => ‖theorem51DyadicBlock x alpha U V W‖ / W) (Set.Ioi 0) := by
  have hk : Integrable (theorem51FiniteScaleKernel x alpha U V) :=
    theorem51FiniteScaleKernel_integrable x alpha U V
  refine (hk.norm.integrableOn).congr_fun ?_ measurableSet_Ioi
  intro W hW
  have hWpos : 0 < W := hW
  show ‖theorem51FiniteScaleKernel x alpha U V W‖ = ‖theorem51DyadicBlock x alpha U V W‖ / W
  by_cases h1 : W < 1
  · rw [theorem51DyadicBlock_zero_small x alpha U V W h1,
      theorem51FiniteScaleKernel_zero_small x alpha U V W h1, norm_zero, zero_div]
  · have hW1 : 1 ≤ W := le_of_not_gt h1
    by_cases h2 : W ≤ x
    · rw [theorem51DyadicBlock_eq_kernel_mul x alpha U V W hU hV hx hW1 h2, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ W),
        theorem51FiniteScaleKernel_norm x alpha U V W hx hW1 h2]
      field_simp
    · have hWx : x < W := lt_of_not_ge h2
      have hout : W ∉ Set.Icc V (x / U) := by
        intro hmem
        have h1 : x / U ≤ x := (div_le_iff₀ (by linarith : (0 : ℝ) < U)).mpr (by nlinarith)
        exact absurd (le_trans hmem.2 h1) (not_le.mpr hWx)
      rw [theorem51DyadicBlock_zero_outside x alpha U V W hU hV hx hUx hVx hUV hout,
        theorem51FiniteScaleKernel_zero_gt_x x alpha U V W hx hWx, norm_zero, zero_div]

/-- The `(0, ∞)` set integral is the interval integral of the scale sum. -/
lemma theorem51_setIntegral_eq_interval (x alpha U V : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hx : 0 < x) (hUx : U < x) (hVx : V < x) (hUV : U * V ≤ x) :
    (∫ W in Set.Ioi (0 : ℝ), ‖theorem51DyadicBlock x alpha U V W‖ / W) =
      ∫ W in V..(x / U), ‖theorem51ScaleSum x alpha U V W‖ / W := by
  have hu : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hVU : V ≤ x / U := (le_div_iff₀ hu).mpr (by nlinarith)
  have hUx' : x / U ≤ x := (div_le_iff₀ hu).mpr (by nlinarith)
  have hf : ∀ W : ℝ, W ∉ Set.Icc V (x / U) → ‖theorem51DyadicBlock x alpha U V W‖ / W = 0 := by
    intro W hW
    rw [theorem51DyadicBlock_zero_outside x alpha U V W hU hV hx hUx hVx hUV hW, norm_zero,
      zero_div]
  have hf' : ∀ W : ℝ, W ∉ Set.Ioi (0 : ℝ) → ‖theorem51DyadicBlock x alpha U V W‖ / W = 0 := by
    intro W hW
    simp only [Set.mem_Ioi, not_lt] at hW
    rw [theorem51DyadicBlock_zero_small x alpha U V W (by linarith), norm_zero, zero_div]
  calc (∫ W in Set.Ioi (0 : ℝ), ‖theorem51DyadicBlock x alpha U V W‖ / W)
      = ∫ W : ℝ, ‖theorem51DyadicBlock x alpha U V W‖ / W :=
        setIntegral_eq_integral_of_forall_compl_eq_zero hf'
    _ = ∫ W in Set.Icc V (x / U), ‖theorem51DyadicBlock x alpha U V W‖ / W :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm
    _ = ∫ W in Set.Icc V (x / U), ‖theorem51ScaleSum x alpha U V W‖ / W := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro W hW
        show ‖theorem51DyadicBlock x alpha U V W‖ / W = ‖theorem51ScaleSum x alpha U V W‖ / W
        have hW1 : 1 ≤ W := hV.trans hW.1
        have hWx : W ≤ x := hW.2.trans hUx'
        rw [theorem51DyadicBlock_eq_kernel_mul x alpha U V W hU hV hx hW1 hWx, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ W),
          theorem51FiniteScaleKernel_norm x alpha U V W hx hW1 hWx]
        field_simp
    _ = ∫ W in V..(x / U), ‖theorem51ScaleSum x alpha U V W‖ / W := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hVU]

end TaoFivePrimes

open TaoFivePrimes MeasureTheory

theorem solution (x alpha U V : ℝ) (hx : 0 < x) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V)
    (hUx : U < x) (hVx : V < x) (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (∀ W : ℝ, W ∉ Set.Icc V (x / U) → ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ = 0)
      ∧ MeasureTheory.IntegrableOn (fun W : ℝ => ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ / W) (Set.Ioi 0)
      ∧ TaoFivePrimes.theorem51TypeII x alpha U V
          ≤ 4 * ∫ W in Set.Ioi (0:ℝ), ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ / W := by
  have hU : 1 ≤ U := by linarith
  have hV : 1 ≤ V := by linarith
  have hUV' : U * V ≤ x := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro W hW
    rw [← theorem51DyadicBlock_eq_tsum x alpha U V W]
    rw [theorem51DyadicBlock_zero_outside x alpha U V W hU hV hx hUx hVx hUV' hW, norm_zero]
  · refine (theorem51DyadicBlock_integrableOn x alpha U V hU hV hx hUx hVx hUV').congr_fun ?_
      measurableSet_Ioi
    intro W hW
    simp only [theorem51DyadicBlock_eq_tsum x alpha U V W]
  · have hI : (∫ W in Set.Ioi (0 : ℝ), ‖∑' d : ℕ, ∑' w : ℕ,
          (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
              ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
              ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
            ((ArithmeticFunction.moebius d : ℤ) : ℂ)
              * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
              * TaoFivePrimes.expCircle (alpha * d * w)
          else 0)‖ / W)
        = ∫ W in Set.Ioi (0 : ℝ), ‖theorem51DyadicBlock x alpha U V W‖ / W := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro W hW
      simp only [theorem51DyadicBlock_eq_tsum x alpha U V W]
    rw [hI, theorem51_setIntegral_eq_interval x alpha U V hU hV hx hUx hVx hUV']
    exact theorem51TypeII_le_scale_integral x alpha U V hx hU hV hUV'
