import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic

namespace TaoFivePrimes

open MeasureTheory

/-- Transfer a bound for sampled first differences of an integrable slope
to second differences of its primitive, without differentiability at corners.
The step identity is the integral form of absolute continuity. -/
theorem second_difference_from_integrated_slope
    (F g : ℝ → ℂ) (a V : ℝ) (N : ℕ)
    (hint : ∀ n : ℕ, IntervalIntegrable (fun t => g (a + 2 * n + t)) volume 0 2)
    (hstep : ∀ n : ℕ, F (a + 2 * (n + 1)) - F (a + 2 * n) =
      ∫ t in (0 : ℝ)..2, g (a + 2 * n + t))
    (hvar : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      (∑ n ∈ Finset.range N, ‖g (a + 2 * (n + 1) + t) - g (a + 2 * n + t)‖) ≤ V) :
    (∑ n ∈ Finset.range N,
      ‖F (a + 2 * (n + 2)) - 2 * F (a + 2 * (n + 1)) + F (a + 2 * n)‖) ≤ 2 * V := by
  let H (n : ℕ) (t : ℝ) := g (a + 2 * (n + 1) + t) - g (a + 2 * n + t)
  have hH (n : ℕ) : IntervalIntegrable (H n) volume 0 2 := by
    simpa [H, Nat.cast_add, Nat.cast_one] using (hint (n + 1)).sub (hint n)
  have he (n : ℕ) : F (a + 2 * (n + 2)) - 2 * F (a + 2 * (n + 1)) + F (a + 2 * n) =
      ∫ t in (0 : ℝ)..2, H n t := by
    have hnext := hstep (n + 1)
    push_cast at hnext
    have hcur := hstep n
    have hsub := intervalIntegral.integral_sub (hint (n + 1)) (hint n)
    push_cast at hsub
    dsimp [H]
    rw [show (fun t : ℝ => g (a + 2 * (↑n + 1) + t) - g (a + 2 * ↑n + t)) =
      (fun t : ℝ => g (a + 2 * (↑n + 1) + t) - g (a + 2 * ↑n + t)) from rfl]
    rw [hsub, ← hnext, ← hcur]
    congr 1 <;> ring
  calc
    _ ≤ ∑ n ∈ Finset.range N, ∫ t in (0 : ℝ)..2, ‖H n t‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [he]
      exact intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ t in (0 : ℝ)..2, ∑ n ∈ Finset.range N, ‖H n t‖ := by
      symm
      exact intervalIntegral.integral_finsetSum (fun n hn => (hH n).norm)
    _ ≤ ∫ t in (0 : ℝ)..2, V := by
      have hsum : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N, ‖H n t‖) volume 0 2 := by
        have hs (s : Finset ℕ) : IntervalIntegrable (fun t => ∑ n ∈ s, ‖H n t‖) volume 0 2 := by
          induction s using Finset.induction with
          | empty => simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 2)
          | @insert n s hn ih =>
              simpa only [Finset.sum_insert hn] using (hH n).norm.add ih
        exact hs (Finset.range N)
      apply intervalIntegral.integral_mono_on (by norm_num)
        hsum intervalIntegrable_const
      exact hvar
    _ = 2 * V := by simp [mul_comm]

/-- Mathlib's bounded-variation quantity directly supplies the sampled bound. -/
theorem second_difference_from_bounded_variation
    (F g : ℝ → ℂ) (a V : ℝ) (N : ℕ) (hV : 0 ≤ V)
    (hint : ∀ n : ℕ, IntervalIntegrable (fun t => g (a + 2 * n + t)) volume 0 2)
    (hstep : ∀ n : ℕ, F (a + 2 * (n + 1)) - F (a + 2 * n) =
      ∫ t in (0 : ℝ)..2, g (a + 2 * n + t))
    (hvar : eVariationOn g Set.univ ≤ ENNReal.ofReal V) :
    (∑ n ∈ Finset.range N,
      ‖F (a + 2 * (n + 2)) - 2 * F (a + 2 * (n + 1)) + F (a + 2 * n)‖) ≤ 2 * V := by
  apply second_difference_from_integrated_slope F g a V N hint hstep
  intro t ht
  have hu : Monotone (fun n : ℕ => a + 2 * (n : ℝ) + t) := by
    intro m n hmn
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have h := (eVariationOn.sum_le (f := g) (s := Set.univ) (n := N)
    hu (fun _ => Set.mem_univ _)).trans hvar
  simp only [edist_dist, dist_eq_norm, Nat.cast_add, Nat.cast_one] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n hn => norm_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hV).mp h

end TaoFivePrimes
