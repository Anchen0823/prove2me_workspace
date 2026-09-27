import Definitions.Def_ZudilinZetaAsymp

/-!
# Zudilin (2001): Lemma 3 — `C₀ > C₁` implies an irrational among (4)

Local mirror of the platform theorem `ZudilinZeta.zudilin_lemma3`.
-/

namespace ZudilinZeta

theorem zudilin_lemma3 (P : Params) (hr : P.r = 3) (τ₀ : ℂ)
    (hroot : charPoly P τ₀ = 0) (him : 0 < τ₀.im)
    (hmax : ∀ τ : ℂ, charPoly P τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re)
    (hre : τ₀.re < (P.eta 0 : ℝ)) (hpi : ∀ k : ℤ, (f0 P τ₀).im ≠ (k : ℝ) * Real.pi)
    (hC : C1 P < C0 P τ₀) :
    ∃ k ∈ Finset.Icc 1 ((P.q - P.r - 2) / 2), Irrational (zetaR (P.r + 2 * k)) := by
  sorry

end ZudilinZeta
