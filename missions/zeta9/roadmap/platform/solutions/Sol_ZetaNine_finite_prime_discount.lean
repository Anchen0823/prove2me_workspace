import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators

theorem solution
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v a : ι → ℕ) (w : ι → ℝ) :
    (∑ i ∈ s, ((v i - 2 * a i : ℕ) : ℝ) * w i) +
      (∑ i ∈ s, ((min (11 * a i - v i) (9 * a i) : ℕ) : ℝ) * w i) =
      9 * ∑ i ∈ s, (a i : ℝ) * w i +
        ∑ i ∈ s, ((v i - 11 * a i : ℕ) : ℝ) * w i := by
  have hpoint (i : ι) :
      v i - 2 * a i + min (11 * a i - v i) (9 * a i) =
        9 * a i + (v i - 11 * a i) := by omega
  calc
    (∑ i ∈ s, ((v i - 2 * a i : ℕ) : ℝ) * w i) +
        (∑ i ∈ s, ((min (11 * a i - v i) (9 * a i) : ℕ) : ℝ) * w i) =
      ∑ i ∈ s, (((v i - 2 * a i : ℕ) : ℝ) +
        ((min (11 * a i - v i) (9 * a i) : ℕ) : ℝ)) * w i := by
          simp only [add_mul, Finset.sum_add_distrib]
    _ = ∑ i ∈ s, (9 * (a i : ℝ) + ((v i - 11 * a i : ℕ) : ℝ)) * w i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hreal :
              ((v i - 2 * a i : ℕ) : ℝ) +
                ((min (11 * a i - v i) (9 * a i) : ℕ) : ℝ) =
              9 * (a i : ℝ) + ((v i - 11 * a i : ℕ) : ℝ) := by
            exact_mod_cast hpoint i
          rw [hreal]
    _ = 9 * ∑ i ∈ s, (a i : ℝ) * w i +
          ∑ i ∈ s, ((v i - 11 * a i : ℕ) : ℝ) * w i := by
          simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
