import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxRecDepth 4096

-- variant A: Nat.mod_lt with big literal subtraction
example (m : ℕ) (hlo : 4 * 10 ^ 14 < m)
    (hB : m ≤ 4 * 10 ^ 18) :
    m ≤ 4 * 10 ^ 14 + (m - 4 * 10 ^ 14) / 1000000 * 1000000 + 1000000 - 1 := by
  have hrem := Nat.mod_lt (m - 4 * 10 ^ 14) (show 0 < 1000000 by norm_num)
  have hsplit := Nat.mod_add_div (m - 4 * 10 ^ 14) 1000000
  omega

-- variant B: same but with `decide`
example (m : ℕ) (hlo : 4 * 10 ^ 14 < m)
    (hB : m ≤ 4 * 10 ^ 18) :
    m ≤ 4 * 10 ^ 14 + (m - 4 * 10 ^ 14) / 1000000 * 1000000 + 1000000 - 1 := by
  have hrem := Nat.mod_lt (m - 4 * 10 ^ 14) (show 0 < 1000000 by decide)
  have hsplit := Nat.mod_add_div (m - 4 * 10 ^ 14) 1000000
  omega
