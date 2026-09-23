import examples.«magic-squares».spencer.SupportExtensionCancellation
import examples.«magic-squares».spencer.SupportedStochasticExistence
import examples.«magic-squares».spencer.MatchingIntervalReduction
import examples.«magic-squares».spencer.SupportIntervalIE

set_option autoImplicit false

namespace MagicSquaresBoundary

open MagicSquaresGeometry MagicSquaresEuler
attribute [local instance] Classical.propDecidable

/-- The matching-support interval Euler relation, proved by projecting the
coordinate faces of its supported doubly stochastic polytope. -/
theorem matchingIntervalEuler_proved (n : ℕ) (hn : 1 ≤ n) : MatchingIntervalEuler n := by
  classical
  intro D B hD hB hDB
  obtain ⟨X, hX, hXs⟩ := exists_doublyStochastic_with_positive_support n D hD
  obtain ⟨Y, hY, hYs⟩ := exists_doublyStochastic_with_positive_support n B hB
  let x : (Fin n × Fin n) → ℝ := fun e => X e.1 e.2
  let y : (Fin n × Fin n) → ℝ := fun e => Y e.1 e.2
  have hxzero (e : Fin n × Fin n) (he : e ∉ D) : x e = 0 := by
    apply le_antisymm _ (nonneg_of_mem_doublyStochastic hX)
    exact le_of_not_gt (fun hp => he ((hXs e.1 e.2).mp hp))
  have hyzero (e : Fin n × Fin n) (he : e ∉ B) : y e = 0 := by
    apply le_antisymm _ (nonneg_of_mem_doublyStochastic hY)
    exact le_of_not_gt (fun hp => he ((hYs e.1 e.2).mp hp))
  have hxP : x ∈ supportedStochasticAffine n B ∧ ∀ e, 0 ≤ x e := by
    apply (mem_supportedStochasticPolytope_iff n B x).mpr
    refine ⟨hX, ?_⟩
    intro e he
    exact hxzero e (fun heD => he (hDB.subset heD))
  have hyP : y ∈ supportedStochasticAffine n B ∧ ∀ e, 0 ≤ y e :=
    (mem_supportedStochasticPolytope_iff n B y).mpr ⟨hY, hyzero⟩
  have hxpos : ∀ e ∈ D, 0 < x e := fun e he => (hXs e.1 e.2).mpr he
  have hnew : ∃ e, e ∉ D ∧ 0 < y e := by
    obtain ⟨e, heB, heD⟩ := Finset.exists_of_ssubset hDB
    exact ⟨e, heD, (hYs e.1 e.2).mpr heB⟩
  have hc := affineOrthant_support_extension_cancellation
    (supportedStochasticAffine n B) D (supportedStochasticPolytope_isCompact n B)
    x y hxP.1 hyP.1 hxpos hxzero hyP.2 hnew
  rw [matching_interval_sum_eq_deletion_sum]
  convert hc using 1
  apply Finset.sum_congr rfl
  intro S _
  rw [supportedStochastic_zeroFace_nonempty_iff_hasPerm n hn B S]
  split_ifs <;> simp

/-- This closes the finite boundary child used by the existing reciprocity
reduction; it has no remaining Euler hypothesis. -/
theorem matchingBoundaryCriterion_proved (n : ℕ) (hn : 1 ≤ n) :
    MatchingBoundaryCriterion n :=
  matchingBoundaryCriterion_of_intervalEuler n hn (matchingIntervalEuler_proved n hn)

end MagicSquaresBoundary
