import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace TaoFivePrimes

lemma odd_reciprocal_range_le (q : ℕ) :
    (∑ k ∈ Finset.range (q + 1), 1 / ((2 * k + 1 : ℕ) : ℝ)) ≤
      1 + (1 / 2 : ℝ) * (harmonic q : ℝ) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.zero_add, Nat.cast_one, div_one]
  have hs : (∑ k ∈ Finset.range q, 1 / ((2 * (k + 1) + 1 : ℕ) : ℝ)) ≤
      (1 / 2 : ℝ) * (harmonic q : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [show (1 / 2 : ℝ) * ((k + 1 : ℕ) : ℝ)⁻¹ =
        1 / (2 * ((k + 1 : ℕ) : ℝ)) by ring]
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
  linarith

/-- A deliberately loose odd harmonic bound, sufficient for q >= 1602. -/
lemma odd_reciprocal_sum_le (q : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ≤ q ∧ Odd d) :
    (∑ d ∈ s, 1 / (d : ℝ)) ≤ 1.5 + 0.5 * Real.log q := by
  let t := (Finset.range (q + 1)).image (fun k => 2 * k + 1)
  have hsub : s ⊆ t := by
    intro d hd
    obtain ⟨hbound, hodd⟩ := hs d hd
    obtain ⟨k, hk⟩ := hodd.exists_bit1
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_range.mpr (by omega), hk.symm⟩
  have he : (∑ d ∈ t, 1 / (d : ℝ)) =
      ∑ k ∈ Finset.range (q + 1), 1 / ((2 * k + 1 : ℕ) : ℝ) := by
    dsimp [t]
    rw [Finset.sum_image]
    intro a ha b hb hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  have hle : (∑ d ∈ s, 1 / (d : ℝ)) ≤ ∑ d ∈ t, 1 / (d : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  rw [he] at hle
  have hH := harmonic_le_one_add_log q
  have hr := odd_reciprocal_range_le q
  linarith

lemma sum_indices_le_square (q : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d < q) :
    (∑ d ∈ s, (d : ℝ)) ≤ (q : ℝ) ^ 2 := by
  have hsub : s ⊆ Finset.range q := fun d hd => Finset.mem_range.mpr (hs d hd)
  have hc : s.card ≤ q := by simpa using Finset.card_le_card hsub
  calc
    _ ≤ ∑ _d ∈ s, (q : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast (hs d hd).le
    _ = (s.card : ℝ) * q := by simp
    _ ≤ (q : ℝ) * q := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)
    _ = _ := by ring

end TaoFivePrimes
