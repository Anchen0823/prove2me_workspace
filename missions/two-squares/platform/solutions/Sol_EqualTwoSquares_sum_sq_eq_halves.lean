-- Public-mission submission for EqualTwoSquares.sum_sq_eq_halves.

import Mathlib

theorem solution {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2)
    (hac : Even (a - c)) (hbd : Even (b - d)) :
    ∃ X Y U V : ℤ,
      X + Y = a ∧ X - Y = c ∧ U - V = b ∧ U + V = d ∧ X * Y = U * V := by
  rcases hac with ⟨k, hk⟩
  rcases hbd with ⟨l, hl⟩
  have hc : c = a - 2 * k := by linarith
  have hd : d = b - 2 * l := by linarith
  rw [hc, hd] at h ⊢
  refine ⟨a - k, k, b - l, -l, ?_, ?_, ?_, ?_, ?_⟩
  · ring
  · ring
  · ring
  · ring
  · nlinarith
