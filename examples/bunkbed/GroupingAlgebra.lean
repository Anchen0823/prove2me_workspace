import examples.bunkbed.GroupingCore

open Bunkbed Bunkbed.Hyper Bunkbed.Sub Finset SimpleGraph Function

set_option maxHeartbeats 200000

namespace Grouping

theorem configuration_subset {I A : Type*} [Fintype I] [DecidableEq I]
    (E : I → Finset A) (S : I → Finset A)
    (hS : S ∈ Fintype.piFinset (fun i => (E i).powerset)) :
    ∀ i, S i ⊆ E i := by
  intro i
  exact Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hS i)

theorem push_two {A B : Type*} [Fintype B]
    (D : Finset A) (st : A → B) (mu : A → ℚ) (P : B → ℚ)
    (hpush : ∀ F : B → ℚ, (∑ a ∈ D, F (st a) * mu a) = ∑ b, F b * P b)
    (F : B → B → ℚ) :
    (∑ a₀ ∈ D, ∑ a₁ ∈ D, F (st a₀) (st a₁) * mu a₀ * mu a₁) =
      ∑ b₀, ∑ b₁, F b₀ b₁ * P b₀ * P b₁ := by
  classical
  calc
    _ = ∑ a₀ ∈ D, ∑ b₁, (F (st a₀) b₁ * mu a₀) * P b₁ := by
      exact Finset.sum_congr rfl (fun a₀ _ => hpush (fun b₁ => F (st a₀) b₁ * mu a₀))
    _ = ∑ b₁, ∑ a₀ ∈ D, (F (st a₀) b₁ * P b₁) * mu a₀ := by
      rw [Finset.sum_comm]
      congr 1
      funext b₁
      exact Finset.sum_congr rfl (fun a₀ _ => mul_right_comm _ _ _)
    _ = ∑ b₁, ∑ b₀, (F b₀ b₁ * P b₁) * P b₀ := by
      exact Finset.sum_congr rfl (fun b₁ _ => hpush (fun b₀ => F b₀ b₁ * P b₁))
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun b₀ _ =>
        Finset.sum_congr rfl (fun b₁ _ => mul_right_comm _ _ _))

theorem pair_state_sum (P : WZ → ℚ) (C : (Fin 6 × Fin 2 → WZ) → ℚ) :
    (∑ φ₀ : Fin 6 → WZ, ∑ φ₁ : Fin 6 → WZ,
      C (twoLevel (φ₀, φ₁)) * (∏ i, P (φ₀ i)) * ∏ i, P (φ₁ i)) =
      ∑ ψ : Fin 6 × Fin 2 → WZ, C ψ * ∏ p, P (ψ p) := by
  rw [← Fintype.sum_prod_type' (fun φ₀ φ₁ : Fin 6 → WZ =>
    C (twoLevel (φ₀, φ₁)) * (∏ i, P (φ₀ i)) * ∏ i, P (φ₁ i))]
  refine Fintype.sum_equiv twoLevelEquiv _ _ ?_
  rintro ⟨φ₀, φ₁⟩
  change C (twoLevel (φ₀, φ₁)) * (∏ i, P (φ₀ i)) * (∏ i, P (φ₁ i)) =
    C (twoLevel (φ₀, φ₁)) * ∏ p, P (twoLevel (φ₀, φ₁) p)
  rw [twoLevel_prod, mul_assoc]

theorem sum_indicator_congr {A : Type*} (D : Finset A) (mu : A → ℚ)
    (ev ev' : A → A → Prop) [DecidableRel ev] [DecidableRel ev']
    (h : ∀ a ∈ D, ∀ b ∈ D, ev a b ↔ ev' a b) :
    (∑ a ∈ D, ∑ b ∈ D, (if ev a b then 1 else 0) * mu a * mu b) =
      ∑ a ∈ D, ∑ b ∈ D, (if ev' a b then 1 else 0) * mu a * mu b := by
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact congrArg (fun z : ℚ => z * mu a * mu b)
    (if_congr (h a ha b hb) rfl rfl)

end Grouping
