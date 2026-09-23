import Mathlib

set_option autoImplicit false

namespace FiniteSupport

open Finset

/-- A weighted finite sum may be restricted to a supported subtype when all
weights outside that support vanish. -/
theorem sum_subtype_filter_eq_sum_filter_of_zero_outside
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q] (w : α → ℚ)
    (hzero : ∀ a, ¬ p a → w a = 0) :
    (∑ a ∈ (Finset.univ.filter fun a : {x // p x} => q a.1), w a.1) =
      ∑ a ∈ (Finset.univ.filter q), w a := by
  classical
  rw [Finset.sum_filter]
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp)
    (fun a => if q a then w a else 0)]
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hp : p a
  · simp [hp]
  · simp [hp, hzero a hp]

end FiniteSupport
