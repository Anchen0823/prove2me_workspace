import Mathlib

open scoped BigOperators

namespace TaoFiniteDifference

/-! Discrete Fourier differentiation for the complementary-correlation
estimate. Integer-indexed finite support keeps all boundary terms explicit. -/

noncomputable def transform (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) : ℂ :=
  a.sum (fun n c => c * fourier n α)

noncomputable def shift (a : ℤ →₀ ℂ) : ℤ →₀ ℂ := a.mapDomain (fun n => n + 1)

noncomputable def difference (a : ℤ →₀ ℂ) : ℤ →₀ ℂ := a - shift a

theorem transform_sub (a b : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    transform (a - b) α = transform a α - transform b α := by
  exact Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _)

theorem transform_shift (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    transform (shift a) α = transform a α * fourier 1 α := by
  unfold transform shift
  rw [Finsupp.sum_mapDomain_index (by intros; simp) (by intros; simp [add_mul])]
  simp only [fourier_add, Finsupp.sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem transform_difference (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    transform (difference a) α = (1 - fourier 1 α) * transform a α := by
  unfold difference
  rw [transform_sub, transform_shift]
  ring

theorem transform_second_difference (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    transform (difference (difference a)) α =
      (1 - fourier 1 α) ^ 2 * transform a α := by
  rw [transform_difference, transform_difference]
  ring

theorem norm_transform_le (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    ‖transform a α‖ ≤ ∑ n ∈ a.support, ‖a n‖ := by
  unfold transform Finsupp.sum
  calc
    _ ≤ ∑ n ∈ a.support, ‖a n * fourier n α‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, show ‖fourier n α‖ = 1 from Circle.norm_coe _]
      simp

theorem second_difference_decay (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    ‖1 - fourier 1 α‖ ^ 2 * ‖transform a α‖ ≤
      ∑ n ∈ (difference (difference a)).support, ‖difference (difference a) n‖ := by
  have h := norm_transform_le (difference (difference a)) α
  rw [transform_second_difference, norm_mul, norm_pow] at h
  exact h

end TaoFiniteDifference
