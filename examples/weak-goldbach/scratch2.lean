import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxRecDepth 8192

-- A: omega with the let-bound b
example (m : ℕ) (hlo : 4 * 10 ^ 14 < m) (hB : m ≤ 4 * 10 ^ 18) :
    4 * 10 ^ 14 + (m - 4 * 10 ^ 14) / 1000000 * 1000000 ≤ m := by
  omega

-- B: explicit subtraction cancellation
example (m : ℕ) (hlo : 4 * 10 ^ 14 < m) (hB : m ≤ 4 * 10 ^ 18) :
    4 * 10 ^ 14 + (m - 4 * 10 ^ 14) / 1000000 * 1000000 ≤ m := by
  have h1 : (m - 4 * 10 ^ 14) / 1000000 * 1000000 ≤ m - 4 * 10 ^ 14 :=
    Nat.div_mul_le_self _ _
  have h2 : 4 * 10 ^ 14 ≤ m := le_of_lt hlo
  omega

-- C: upper bound step
example (m : ℕ) (hlo : 4 * 10 ^ 14 < m) (hB : m ≤ 4 * 10 ^ 18) :
    m ≤ 4 * 10 ^ 14 + ((m - 4 * 10 ^ 14) / 1000000 + 1) * 1000000 - 1 := by
  have hrem := Nat.mod_lt (m - 4 * 10 ^ 14) (show 0 < 1000000 by norm_num)
  have hsplit := Nat.mod_add_div (m - 4 * 10 ^ 14) 1000000
  omega

-- D: index bound with let-free form
example (m : ℕ) (hlo : 4 * 10 ^ 14 < m) (hB : m ≤ 4 * 10 ^ 18) :
    (m - 4 * 10 ^ 14) / 1000000 < 4000000000001 := by
  have hm : m - 4 * 10 ^ 14 ≤ 4 * 10 ^ 18 - 4 * 10 ^ 14 := Nat.sub_le_sub_right hB _
  have h1 : (m - 4 * 10 ^ 14) / 1000000 ≤ (4 * 10 ^ 18 - 4 * 10 ^ 14) / 1000000 :=
    Nat.div_le_div_right hm
  have h2 : (4 * 10 ^ 18 - 4 * 10 ^ 14) / 1000000 = 3999600000000 := by norm_num
  omega

-- E: the max/le_min membership step
example (m : ℕ) (hlo : 4 * 10 ^ 14 < m) (hB : m ≤ 4 * 10 ^ 18)
    (b : ℕ) (hlo' : 4 * 10 ^ 14 + b * 1000000 ≤ m)
    (hhi' : m ≤ 4 * 10 ^ 14 + (b + 1) * 1000000 - 1) :
    max 4 (4 * 10 ^ 14 + b * 1000000) ≤ m := by
  have h4 : 4 ≤ m := by omega
  exact max_le h4 hlo'

-- F: the square bound
example (b : ℕ) :
    min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1) ≤ 2000000000 ^ 2 := by
  calc
    min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1) ≤ 4 * 10 ^ 18 :=
      min_le_left _ _
    _ = 2000000000 ^ 2 := by norm_num
