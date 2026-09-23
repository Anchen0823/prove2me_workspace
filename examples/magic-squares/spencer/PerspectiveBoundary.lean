import Mathlib
import examples.«magic-squares».spencer.OrthantFace

set_option autoImplicit false

namespace MagicSquaresEuler

/-- The far coordinate boundary viewed from a point positive on every index
in `D`. All its points are nonnegative on `D` and have a zero there. -/
def coordinateBackBoundary {ι : Type*} (D : Set ι) : Set (ι → ℝ) :=
  {x | (∀ i ∈ D, 0 ≤ x i) ∧ ∃ i ∈ D, x i = 0}

/-- A ray from a point positive on `D` meets its far coordinate boundary at
most once. This is the intersection-preservation input for perspective images. -/
theorem coordinateBackBoundary_ray_unique {ι : Type*} (D : Set ι)
    (q x y : ι → ℝ) (hq : ∀ i ∈ D, 0 < q i)
    (hx : x ∈ coordinateBackBoundary D) (hy : y ∈ coordinateBackBoundary D)
    (t : ℝ) (ht : 0 < t) (hxy : ∀ i, x i = q i + t * (y i - q i)) :
    t = 1 ∧ x = y := by
  obtain ⟨i, hiD, hxi⟩ := hx.2
  obtain ⟨j, hjD, hyj⟩ := hy.2
  have hqi := hq i hiD
  have hqj := hq j hjD
  have hyi := hy.1 i hiD
  have hxj := hx.1 j hjD
  have hi := hxy i
  have hj := hxy j
  have ht1 : t = 1 := by
    have hprod : 0 ≤ t * y i := mul_nonneg ht.le hyi
    have hle : t ≤ 1 := by nlinarith
    have hge : 1 ≤ t := by nlinarith
    exact le_antisymm hle hge
  refine ⟨ht1, ?_⟩
  funext k
  simpa [ht1] using hxy k

/-- Normalized rays are injective on this boundary whenever the denominators
are positive. A separating affine functional supplies these denominators. -/
theorem coordinateBackBoundary_normalize_injOn {ι : Type*} (D : Set ι)
    (q : ι → ℝ) (d : (ι → ℝ) → ℝ) (hq : ∀ i ∈ D, 0 < q i) :
    Set.InjOn (fun x i => (x i - q i) / d x)
      {x | x ∈ coordinateBackBoundary D ∧ 0 < d x} := by
  intro x hx y hy heq
  apply (coordinateBackBoundary_ray_unique D q x y hq hx.1 hy.1
    (d x / d y) (div_pos hx.2 hy.2) ?_).2
  intro i
  have hc := (div_eq_div_iff (ne_of_gt hx.2) (ne_of_gt hy.2)).mp (congrFun heq i)
  field_simp [ne_of_gt hy.2]
  nlinarith

/-- If no zero coordinate faces towards the external point, the nonnegative
ray can be extended slightly past the current point. -/
theorem exists_nonnegative_ray_extension {ι : Type*} [Fintype ι]
    (q x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hzero : ∀ i, x i = 0 → q i ≤ 0) :
    ∃ t : ℝ, 1 < t ∧ ∀ i, 0 ≤ q i + t * (x i - q i) := by
  let y : ι → ℝ := fun i => max (q i - x i) 0
  have hy : ∀ i, 0 ≤ y i := fun i => le_max_right _ _
  have hz : ∀ i, x i = 0 → y i = 0 := by
    intro i hi
    simp only [y, hi, sub_zero]
    exact max_eq_right (hzero i hi)
  obtain ⟨a, ha, hab⟩ :=
    MagicSquaresGeometry.exists_pos_smul_le_of_zero_imp x y hx hy hz
  refine ⟨1 + a, by linarith, ?_⟩
  intro i
  have hle : a * (q i - x i) ≤ x i :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) ha.le).trans (hab i)
  nlinarith

end MagicSquaresEuler
