import Mathlib
import Definitions.Def_ZudilinZetaSetup

/-!
# Zudilin (2001): the series `zetaR k` identifies with Mathlib's `riemannZeta` at `k ≥ 2`

This is a frontier child of the mission goal `FCP.Zeta.zudilin_five_seven_nine_eleven`.
It bridges the elementary series `zetaR k = ∑ₙ (n+1)⁻ᵏ` (used throughout the
`ZudilinZeta` formalization) with Mathlib's complex `riemannZeta`, whose
`formal_statement` in the mission goal mentions `riemannZeta` directly.
-/

namespace ZudilinZeta

theorem zetaR_eq_riemannZeta (k : ℕ) (hk : 2 ≤ k) :
    riemannZeta (k : ℂ) = (zetaR k : ℂ) := by
  sorry

end ZudilinZeta
