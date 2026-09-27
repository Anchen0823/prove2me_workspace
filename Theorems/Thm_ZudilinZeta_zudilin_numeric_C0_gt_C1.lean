import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13

/-!
# Zudilin (2001): the computed constants — `C₀ = 227.58019641… > C₁ = 226.24944266…`

Local mirror of the platform theorem `ZudilinZeta.zudilin_numeric_C0_gt_C1`.
-/

namespace ZudilinZeta

theorem zudilin_numeric_C0_gt_C1 (τ₀ : ℂ)
    (hroot : charPoly params13 τ₀ = 0) (him : 0 < τ₀.im)
    (hmax : ∀ τ : ℂ, charPoly params13 τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re) :
    (227.58019641 ≤ C0 params13 τ₀ ∧ C0 params13 τ₀ < 227.58019642) ∧
      (226.24944266 ≤ C1 params13 ∧ C1 params13 < 226.24944267) ∧
      C1 params13 < C0 params13 τ₀ := by
  sorry

end ZudilinZeta
