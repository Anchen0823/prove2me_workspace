import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13

/-!
# Zudilin (2001): existence of the saddle point for the parameters `(3, 13)`

This is a frontier child of the mission goal `FCP.Zeta.zudilin_five_seven_nine_eleven`.
It packages the analytic content of Lemma 2 of Zudilin's note for the specific
parameter set `params13` (`r = 3`, `q = 13`, `η₀ = 91`, …): the saddle point `τ₀`
of the saddle-point equation, lying in the upper half-plane, of maximal real part
among the upper half-plane roots, with `Re τ₀ < η₀` and `Im f₀(τ₀)` outside the
lattice `πℤ` (so that the leading asymptotic coefficient of `|Fₙ|` does not vanish).
-/

namespace ZudilinZeta

theorem exists_saddle_root_params13 :
    ∃ τ₀ : ℂ, charPoly params13 τ₀ = 0 ∧ 0 < τ₀.im ∧
      (∀ τ : ℂ, charPoly params13 τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re) ∧
      τ₀.re < (params13.eta 0 : ℝ) ∧
      (∀ k : ℤ, (f0 params13 τ₀).im ≠ (k : ℝ) * Real.pi) := by
  sorry

end ZudilinZeta
