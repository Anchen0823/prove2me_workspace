import Definitions.Def_TaoFivePrimes_ArcSplit
open MeasureTheory TaoFivePrimes
open scoped BigOperators ComplexConjugate

theorem TaoFivePrimes.eta1_complementary_correlation (x : ℕ)
    (hr_lower : 1 / (2 * (x : ℝ)) ≤ T0 / (3.6 * Real.pi * (x : ℝ)))
    (hr_upper : T0 / (3.6 * Real.pi * (x : ℝ)) ≤ 1 / 2)
    (hc8 : (10 ^ 8 : ℝ) ≤ (1 / 10 : ℝ) * x)
    (hneat : (10 ^ 4 : ℝ) * (3 / 2 : ℝ) ≤ x)
    (halamo : 5 * (3 / 2 : ℝ) ≤ Real.log ((1 / 10 : ℝ) * x))
    (h10q : (10 ^ 8 : ℝ) * (9 / 4 : ℝ) ≤ x)
    (hr0b : 20 * 60 * Real.sqrt (3 / 2 : ℝ) ≤ T0 / (3.6 * Real.pi))
    (ε : ℝ) (hε : |ε| ≤ 0.02)
    (hmass : (∑ n ∈ Finset.range (x + 1),
      siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
        (2 / 3 : ℝ) * (1 + ε) * x) :
    ‖∫ α in (majorArc x)ᶜ, S1 x α *
      conj (TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α)
        ∂AddCircle.haarAddCircle‖ ≤
      0.01 * ((2 / 3 : ℝ) * (1 + ε) * x) := by sorry
