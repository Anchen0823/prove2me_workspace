import Definitions.Def_TaoFivePrimes_ArcSplit
import Mathlib.MeasureTheory.Integral.Bochner.Set

open scoped BigOperators ArithmeticFunction.vonMangoldt
open MeasureTheory

namespace TaoFivePrimes

theorem rosser_schoenfeld_psi_bound :
    ∀ x : ℕ, 0 < x →
      (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ)) <
        1.03883 * (x : ℝ) := by
  sorry

end TaoFivePrimes