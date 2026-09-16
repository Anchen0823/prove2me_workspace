import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxRecDepth 4096

-- A: let-bound b, explicit h2 then omega
example (m : ℕ) (hlo : 4 * 10 ^ 14 < m) (hB : m ≤ 4 * 10 ^ 18) :
    4 * 10 ^ 14 + (m - 4 * 10 ^ 14) / 1000000 * 1000000 ≤ m := by
  let b := (m - 4 * 10 ^ 14) / 1000000
  have h1 : b * 1000000 ≤ m - 4 * 10 ^ 14 := by
    dsimp [b]
    exact Nat.div_mul_le_self _ _
  have h2 : 4 * 10 ^ 14 ≤ m := le_of_lt hlo
  omega

-- B: let-bound b, statement in terms of b
example (m : ℕ) (hlo : 4 * 10 ^ 14 < m) (hB : m ≤ 4 * 10 ^ 18) :
    4 * 10 ^ 14 + (m - 4 * 10 ^ 14) / 1000000 * 1000000 ≤ m := by
  let b := (m - 4 * 10 ^ 14) / 1000000
  change 4 * 10 ^ 14 + b * 1000000 ≤ m
  have h1 : b * 1000000 ≤ m - 4 * 10 ^ 14 := by
    dsimp only [b]
    exact Nat.div_mul_le_self _ _
  have h2 : 4 * 10 ^ 14 ≤ m := le_of_lt hlo
  omega

-- C: no let, whole proof inline
example (m : ℕ) (hlo : 4 * 10 ^ 14 < m) (hB : m ≤ 4 * 10 ^ 18) :
    4 * 10 ^ 14 + (m - 4 * 10 ^ 14) / 1000000 * 1000000 ≤ m := by
  have h1 : (m - 4 * 10 ^ 14) / 1000000 * 1000000 ≤ m - 4 * 10 ^ 14 :=
    Nat.div_mul_le_self _ _
  have h2 : 4 * 10 ^ 14 ≤ m := le_of_lt hlo
  omega
