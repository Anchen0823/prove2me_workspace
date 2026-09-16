import Mathlib

lemma min_add_const_le (a b C : ℝ) (hC : 0 ≤ C) :
    min (a + C) b ≤ min a b + C := by
  rcases le_total a b with hab | hba
  · rcases le_total b (a + C) with h | h
    · rw [min_eq_left hab, min_eq_right h]; exact h
    · rw [min_eq_left hab, min_eq_left h]
  · have hb' : b ≤ a + C := by linarith
    rw [min_eq_right hba, min_eq_right hb']
    linarith
