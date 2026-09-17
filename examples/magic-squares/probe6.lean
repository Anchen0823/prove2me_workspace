import Mathlib

example (a b t : ℕ) (h : min a b = 0) : a = 0 ∨ b = 0 := by
  omega

example (a b c t : ℕ) (h1 : a + b + c = t) (h2 : min a b = 0) : a = 0 ∨ b = 0 := by
  omega
