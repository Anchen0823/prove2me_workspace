import examples.«magic-squares».spencer.PerspectiveBoundary

set_option autoImplicit false

namespace MagicSquaresEuler

theorem compact_ray_last {ι : Type*} [Fintype ι]
    (K : Set (ι → ℝ)) (hK : IsCompact K) (q x : ι → ℝ)
    (hx : x ∈ K) (hne : x ≠ q) :
    ∃ t : ℝ, 1 ≤ t ∧ q + t • (x - q) ∈ K ∧
      ∀ s : ℝ, q + s • (x - q) ∈ K → s ≤ t := by
  have he : Topology.IsClosedEmbedding (fun t : ℝ => q + t • (x - q)) :=
    (Homeomorph.addLeft q).isClosedEmbedding.comp
      (isClosedEmbedding_smul_left (sub_ne_zero.mpr hne))
  have hc := he.isCompact_preimage hK
  have h1 : (1 : ℝ) ∈ (fun t : ℝ => q + t • (x - q)) ⁻¹' K := by
    simpa using hx
  obtain ⟨t, ht, hmax⟩ := hc.exists_isGreatest ⟨1, h1⟩
  exact ⟨t, hmax h1, ht, fun s hs => hmax hs⟩

/-- A compact affine orthant section has a far boundary point on every ray
from an external affine point nonpositive off `D`. -/
theorem affine_orthant_ray_hits_backBoundary {ι : Type*} [Fintype ι]
    (A : AffineSubspace ℝ (ι → ℝ)) (D : Set ι) (q : ι → ℝ)
    (hK : IsCompact {x : ι → ℝ | x ∈ A ∧ ∀ i, 0 ≤ x i})
    (hqA : q ∈ A) (hqout : ¬ ∀ i, 0 ≤ q i)
    (hqD : ∀ i, i ∉ D → q i ≤ 0)
    (x : ι → ℝ) (hxA : x ∈ A) (hx : ∀ i, 0 ≤ x i) :
    ∃ t : ℝ, 1 ≤ t ∧
      q + t • (x - q) ∈ A ∧
      (∀ i, 0 ≤ (q + t • (x - q)) i) ∧
      q + t • (x - q) ∈ coordinateBackBoundary D := by
  classical
  have hne : x ≠ q := by rintro rfl; exact hqout hx
  obtain ⟨t, ht, hz, hmax⟩ := compact_ray_last _ hK q x ⟨hxA, hx⟩ hne
  refine ⟨t, ht, hz.1, hz.2, (fun i _ => hz.2 i), ?_⟩
  by_contra hnone
  have hzero (i : ι) (hi : (q + t • (x - q)) i = 0) : q i ≤ 0 := by
    by_cases hiD : i ∈ D
    · exact False.elim (hnone ⟨i, hiD, hi⟩)
    · exact hqD i hiD
  obtain ⟨u, hu, hunonneg⟩ := exists_nonnegative_ray_extension q
    (q + t • (x - q)) hz.2 hzero
  have hid : q + u • ((q + t • (x - q)) - q) = q + (u * t) • (x - q) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hA : q + (u * t) • (x - q) ∈ A := by
    simpa only [vsub_eq_sub, vadd_eq_add, add_comm] using
      A.smul_vsub_vadd_mem (u * t) hxA hqA hqA
  have hn : ∀ i, 0 ≤ (q + (u * t) • (x - q)) i := by
    rw [← hid]
    exact hunonneg
  have hle := hmax (u * t) ⟨hA, hn⟩
  nlinarith

end MagicSquaresEuler
