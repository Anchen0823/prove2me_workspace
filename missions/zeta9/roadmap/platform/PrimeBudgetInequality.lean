import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace ZetaNine

theorem finite_prime_budget
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v a : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∑ i ∈ s, ((v i - 2 * a i : ℕ) : ℝ) * w i ≤
      9 * ∑ i ∈ s, (a i : ℝ) * w i +
        ∑ i ∈ s, ((v i - 11 * a i : ℕ) : ℝ) * w i := by sorry

end ZetaNine
