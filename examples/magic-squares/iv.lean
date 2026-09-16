import Mathlib
import Definitions.Def_MagicSquaresParam3

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

namespace MagicSquares

def paramLo (e a : ℕ) : ℕ := if a ≤ e then e - a else a - e
def paramHi (e a : ℕ) : ℕ := if a ≤ e then e + a else 3 * e - a

theorem isParam3_iff_interval (e a c : ℕ) (ha : a ≤ 2 * e) :
    IsParam3 e a c ↔ paramLo e a ≤ c ∧ c ≤ paramHi e a := by
  unfold IsParam3 paramLo paramHi
  by_cases hle : a ≤ e
  · simp [hle]
    constructor <;> intro h <;> omega
  · simp [hle]
    constructor <;> intro h <;> omega

end MagicSquares
