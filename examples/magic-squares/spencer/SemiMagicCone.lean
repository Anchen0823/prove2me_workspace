import examples.«magic-squares».spencer.OrthantFace

set_option autoImplicit false

namespace MagicSquaresGeometry

open Finset

/-- Real matrices whose rows and columns have one common line sum. -/
def semiMagicSubspace (n : ℕ) : Submodule ℝ ((Fin n × Fin n) → ℝ) where
  carrier := {x | ∃ s : ℝ,
    (∀ i, ∑ j, x (i, j) = s) ∧ (∀ j, ∑ i, x (i, j) = s)}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩ <;> intro i <;> simp
  add_mem' := by
    rintro x y ⟨sx, hxr, hxc⟩ ⟨sy, hyr, hyc⟩
    refine ⟨sx + sy, ?_, ?_⟩
    · intro i
      simp only [Pi.add_apply, sum_add_distrib, hxr i, hyr i]
    · intro j
      simp only [Pi.add_apply, sum_add_distrib, hxc j, hyc j]
  smul_mem' := by
    rintro a x ⟨s, hxr, hxc⟩
    refine ⟨a * s, ?_, ?_⟩
    · intro i
      change ∑ j, a * x (i, j) = a * s
      rw [← Finset.mul_sum, hxr i]
    · intro j
      change ∑ i, a * x (i, j) = a * s
      rw [← Finset.mul_sum, hxc j]

theorem exists_pos_common_line_sum_of_nonneg_ne_zero {n : ℕ}
    {x : (Fin n × Fin n) → ℝ} (hx : x ∈ semiMagicSubspace n)
    (hnonneg : ∀ e, 0 ≤ x e) (hne : x ≠ 0) :
    ∃ s : ℝ, 0 < s ∧
      (∀ i, ∑ j, x (i, j) = s) ∧ (∀ j, ∑ i, x (i, j) = s) := by
  obtain ⟨s, hrow, hcol⟩ := hx
  have hentry : ∃ i j, x (i, j) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    funext e
    rcases e with ⟨i, j⟩
    exact h i j
  obtain ⟨i, j, hij⟩ := hentry
  have hpos : 0 < x (i, j) := lt_of_le_of_ne (hnonneg (i, j)) (Ne.symm hij)
  have hle : x (i, j) ≤ ∑ k, x (i, k) :=
    Finset.single_le_sum (fun k _ => hnonneg (i, k)) (Finset.mem_univ j)
  refine ⟨s, hpos.trans_le (by simpa [hrow i] using hle), hrow, hcol⟩

/-- Divide a nonzero nonnegative semi-magic matrix by its common line sum. -/
noncomputable def normalizedSemiMagic {n : ℕ} (x : (Fin n × Fin n) → ℝ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => x (i, j) / s

theorem normalizedSemiMagic_mem_doublyStochastic {n : ℕ}
    {x : (Fin n × Fin n) → ℝ} {s : ℝ} (hs : 0 < s)
    (hnonneg : ∀ e, 0 ≤ x e) (hrow : ∀ i, ∑ j, x (i, j) = s)
    (hcol : ∀ j, ∑ i, x (i, j) = s) :
    normalizedSemiMagic x s ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact div_nonneg (hnonneg (i, j)) hs.le
  · intro i
    change (∑ j, x (i, j) / s) = 1
    rw [← Finset.sum_div, hrow i, div_self hs.ne']
  · intro j
    change (∑ i, x (i, j) / s) = 1
    rw [← Finset.sum_div, hcol j, div_self hs.ne']

theorem normalizedSemiMagic_pos_iff {n : ℕ} {x : (Fin n × Fin n) → ℝ} {s : ℝ}
    (hs : 0 < s) (i j : Fin n) :
    0 < normalizedSemiMagic x s i j ↔ 0 < x (i, j) := by
  simp only [normalizedSemiMagic]
  exact div_pos_iff_of_pos_right hs

end MagicSquaresGeometry
