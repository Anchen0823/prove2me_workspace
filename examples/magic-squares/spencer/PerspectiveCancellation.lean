import examples.«magic-squares».spencer.PerspectiveIntersections
import examples.«magic-squares».spencer.FiniteCoordinateValuation
import examples.«magic-squares».spencer.FiniteCoverIndicator

set_option autoImplicit false

namespace MagicSquaresEuler

attribute [local instance] Classical.propDecidable

/-- The coordinate-face alternating sum vanishes when an external affine point
is positive on the selected coordinates and nonpositive on all others. -/
theorem affineOrthant_coordinate_cancellation {ι : Type*} [Fintype ι]
    (A : AffineSubspace ℝ (ι → ℝ)) (D : Finset ι) (q : ι → ℝ)
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hK : IsCompact {x : ι → ℝ | x ∈ A ∧ ∀ i, 0 ≤ x i})
    (hqA : q ∈ A) (hqout : ¬ ∀ i, 0 ≤ q i)
    (hqpos : ∀ i ∈ D, 0 < q i) (hqneg : ∀ i, i ∉ D → q i ≤ 0)
    (hpos : ∀ x : ι → ℝ, x ∈ A → (∀ i, 0 ≤ x i) → 0 < ℓ (x - q)) :
    (∑ S ∈ D.powerset, if
      ({x : ι → ℝ | (x ∈ A ∧ ∀ i, 0 ≤ x i) ∧ ∀ i ∈ S, x i = 0}).Nonempty
      then (-1 : ℚ) ^ S.card else 0) = 0 := by
  classical
  let P : Set (ι → ℝ) := {x | x ∈ A ∧ ∀ i, 0 ≤ x i}
  let Q : Finset ι → Set (ι → ℝ) := fun S => P ∩ {x | ∀ i ∈ S, x i = 0}
  let f : (ι → ℝ) → (ι → ℝ) := fun x => (ℓ (x - q))⁻¹ • (x - q)
  let H : Set (ι → ℝ) := f '' P
  let F : ι → Set (ι → ℝ) := fun i => f '' {x | x ∈ P ∧ x i = 0}
  have hPconv : Convex ℝ P := by
    intro x hx y hy a b ha hb hab
    refine ⟨A.convex hx.1 hy.1 ha hb hab, ?_⟩
    intro i
    exact add_nonneg (mul_nonneg ha (hx.2 i)) (mul_nonneg hb (hy.2 i))
  have hQcompact (S : Finset ι) : IsCompact (Q S) := by
    apply hK.inter_right
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i : ι => isClosed_iInter fun _ : i ∈ S =>
      isClosed_eq (continuous_apply i : Continuous (fun x : ι → ℝ => x i))
        (continuous_const : Continuous (fun _ : ι → ℝ => (0 : ℝ)))
  have hQconv (S : Finset ι) : Convex ℝ (Q S) := by
    apply hPconv.inter
    intro x hx y hy a b ha hb hab i hi
    change a * x i + b * y i = 0
    rw [hx i hi, hy i hi]
    ring
  have hden (x : ι → ℝ) (hx : x ∈ P) : 0 < ℓ (x - q) := hpos x hx.1 hx.2
  have hc (S : Finset ι) : IsCompact (f '' Q S) :=
    compact_perspective_image (Q S) q ℓ (hQcompact S) (fun x hx => hden x hx.1)
  have hv (S : Finset ι) : Convex ℝ (f '' Q S) :=
    convex_perspective_image (Q S) q ℓ (hQconv S) (fun x hx => hden x hx.1)
  have hcover : ∀ z ∈ H, ∃ i ∈ D, z ∈ F i := by
    intro z hz
    have he := perspective_shadow_eq_backBoundary A (↑D : Set ι) q ℓ hK hqA
      hqout hqneg hpos
    have hz' : z ∈ f '' (P ∩ coordinateBackBoundary (↑D : Set ι)) := by
      rw [he]
      exact hz
    obtain ⟨x, ⟨hxP, hxD⟩, hfx⟩ := hz'
    obtain ⟨i, hi, hxi⟩ := hxD.2
    exact ⟨i, hi, x, ⟨hxP, hxi⟩, hfx⟩
  have hinter (S : Finset ι) (hS : S ⊆ D) :
      f '' Q S = {z | z ∈ H ∧ ∀ i ∈ S, z ∈ F i} :=
    perspective_image_coordinate_intersections P D S q ℓ hS
      (fun x hx i _ => hx.2 i) hqpos hden
  have hpowers : Finset.univ.filter (fun S : Finset ι => S ⊆ D) = D.powerset := by
    ext S
    simp
  let w : Finset ι → ℚ := fun S => if S ⊆ D then (-1 : ℚ) ^ S.card else 0
  have hrelation (z : ι → ℝ) :
      (∑ S : Finset ι, if z ∈ f '' Q S then w S else 0) = 0 := by
    have heq : (∑ S : Finset ι, if z ∈ f '' Q S then w S else 0) =
        ∑ S ∈ D.powerset, if z ∈ H ∧ ∀ i ∈ S, z ∈ F i
          then (-1 : ℚ) ^ S.card else 0 := by
      rw [← hpowers, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S ⊆ D
      · rw [hinter S hS]
        simp only [w, hS, if_true, Set.mem_setOf_eq]
      · simp [w, hS]
    rw [heq]
    convert finiteCover_alternating_indicator_zero D H F hcover z using 1
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> rfl
  have htotal := finiteCoordinate_indicator_relation ι (fun S => f '' Q S) w hc hv hrelation
  have heq : (∑ S : Finset ι, if (f '' Q S).Nonempty then w S else 0) =
      ∑ S ∈ D.powerset, if (Q S).Nonempty then (-1 : ℚ) ^ S.card else 0 := by
    rw [← hpowers, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hS : S ⊆ D <;> simp [w, hS, Set.image_nonempty]
  rw [heq] at htotal
  exact htotal

end MagicSquaresEuler
