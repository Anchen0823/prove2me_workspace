import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators

theorem solution
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v a : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∑ i ∈ s, ((v i - 2 * a i : ℕ) : ℝ) * w i ≤
      9 * ∑ i ∈ s, (a i : ℝ) * w i +
        ∑ i ∈ s, ((v i - 11 * a i : ℕ) : ℝ) * w i := by
  calc
    ∑ i ∈ s, ((v i - 2 * a i : ℕ) : ℝ) * w i ≤
        ∑ i ∈ s, (9 * (a i : ℝ) + ((v i - 11 * a i : ℕ) : ℝ)) * w i := by
          apply Finset.sum_le_sum
          intro i hi
          have hiNat : v i - 2 * a i ≤ 9 * a i + (v i - 11 * a i) := by omega
          have hiReal : ((v i - 2 * a i : ℕ) : ℝ) ≤
              9 * (a i : ℝ) + ((v i - 11 * a i : ℕ) : ℝ) := by
            exact_mod_cast hiNat
          exact mul_le_mul_of_nonneg_right hiReal (hw i hi)
    _ = 9 * ∑ i ∈ s, (a i : ℝ) * w i +
          ∑ i ∈ s, ((v i - 11 * a i : ℕ) : ℝ) * w i := by
          simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
