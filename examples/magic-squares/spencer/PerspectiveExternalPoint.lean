import examples.«magic-squares».spencer.OrthantFace

set_option autoImplicit false

namespace MagicSquaresEuler

/-- A point supported positively on `D` and a nonnegative point with a new
positive coordinate determine an affine external point with the desired signs. -/
theorem exists_affine_external_point {ι : Type*} [Fintype ι]
    (A : AffineSubspace ℝ (ι → ℝ)) (D : Finset ι) (x y : ι → ℝ)
    (hxA : x ∈ A) (hyA : y ∈ A)
    (hxpos : ∀ i ∈ D, 0 < x i) (hxzero : ∀ i, i ∉ D → x i = 0)
    (hy : ∀ i, 0 ≤ y i) (hnew : ∃ i, i ∉ D ∧ 0 < y i) :
    ∃ q : ι → ℝ, q ∈ A ∧ (∀ i ∈ D, 0 < q i) ∧
      (∀ i, i ∉ D → q i ≤ 0) ∧ ¬ ∀ i, 0 ≤ q i := by
  classical
  obtain ⟨a, ha, hab⟩ := MagicSquaresGeometry.exists_pos_smul_le_of_zero_imp
    (fun i : D => x i) (fun i : D => y i)
    (fun i => (hxpos i i.property).le) (fun i => hy i)
    (fun i hi => False.elim ((ne_of_gt (hxpos i i.property)) hi))
  let q : ι → ℝ := (1 + a) • x - a • y
  have hqA : q ∈ A := by
    have he : q = a • (x - y) + x := by
      ext i
      simp only [q, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    rw [he]
    exact A.smul_vsub_vadd_mem a hxA hyA hxA
  refine ⟨q, hqA, ?_, ?_, ?_⟩
  · intro i hi
    have hb := hab ⟨i, hi⟩
    have hp := hxpos i hi
    change 0 < (1 + a) * x i - a * y i
    have hm := mul_pos ha hp
    dsimp only at hb
    nlinarith
  · intro i hi
    change (1 + a) * x i - a * y i ≤ 0
    rw [hxzero i hi]
    nlinarith [mul_nonneg ha.le (hy i)]
  · intro hq
    obtain ⟨i, hi, hiy⟩ := hnew
    have hqi := hq i
    change 0 ≤ (1 + a) * x i - a * y i at hqi
    rw [hxzero i hi] at hqi
    nlinarith [mul_pos ha hiy]

end MagicSquaresEuler
