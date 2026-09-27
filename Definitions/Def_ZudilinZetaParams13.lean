import Definitions.Def_ZudilinZetaSetup

/-!
# Zudilin (2001): the parameter set used to prove the theorem

`r = 3`, `q = 13`, `η₀ = 91`, `η₁ = η₂ = η₃ = 27`, `η₄ = 29`, `η₅ = 30`, `η₆ = 31`, …,
`η₁₂ = 37`, `η₁₃ = 38`.
-/

namespace ZudilinZeta

/-- The parameters `η₀ = 91`, `η₁ = η₂ = η₃ = 27`, and `η_j = 25 + j` for `4 ≤ j ≤ 13`
(so `η₄ = 29`, `η₅ = 30`, `η₆ = 31`, …, `η₁₂ = 37`, `η₁₃ = 38`). -/
def eta13 (j : ℕ) : ℕ :=
  if j = 0 then 91 else if j ≤ 3 then 27 else if j ≤ 13 then 25 + j else 0

/-- The admissible parameter set `r = 3`, `q = 13` with the `η`'s of `eta13`,
used in Zudilin's note to prove the theorem. -/
def params13 : Params where
  q := 13
  r := 3
  eta := eta13
  q_odd := by decide
  r_odd := by decide
  q_ge := by decide
  eta_pos := by decide
  eta_mono := by decide
  eta_lt := by decide
  sum_le := by decide

end ZudilinZeta
