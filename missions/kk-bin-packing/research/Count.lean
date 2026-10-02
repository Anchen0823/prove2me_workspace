import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2

open KKBinPacking.Shared KKBinPacking.GeometricGrouping
open scoped BigOperators

namespace KKContribution

lemma principalConfigs_card (x : Multiset ℝ →₀ ℝ) :
    (principalConfigs x).card = principalCount x := by
  classical
  simp [principalConfigs, principalCount]

lemma principal_bins_card (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (tr : Alg2Trace k g I) (i : ℕ) (hi : i < tr.t) :
    (tr.Bp i).card = principalCount (tr.x i) := by
  exact (Multiset.card_eq_card_of_rel (tr.Bp_config i hi)).trans
    (principalConfigs_card _)

lemma step3_card_bound (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (tr : Alg2Trace k g I) :
    (Multiset.card (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) : ℝ) ≤
      ((∑ i ∈ Finset.range tr.t, principalCount (tr.x i) : ℕ) : ℝ) +
        tr.t * (2 * (k : ℝ) * (2 + Real.log (1 / g))) +
        2 + (2 / (1 - 1 / (k : ℝ))) * Real.log (1 / g) := by
  classical
  have hc : (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3).card =
      (∑ i ∈ Finset.range tr.t, (principalCount (tr.x i) + (tr.PJ' i).card)) +
        tr.P3.card := by
    simp only [alg2Step3Bins, Multiset.card_add, Multiset.card_sum, Multiset.card_map]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [principal_bins_card k g I tr i (Finset.mem_range.mp hi)]
  rw [hc]
  push_cast
  have hJ : (∑ i ∈ Finset.range tr.t, ((tr.PJ' i).card : ℝ)) ≤
      tr.t * (2 * (k : ℝ) * (2 + Real.log (1 / g))) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range tr.t, (2 * (k : ℝ) * (2 + Real.log (1 / g))) := by
        exact Finset.sum_le_sum fun i hi => tr.PJ'_card i (Finset.mem_range.mp hi)
      _ = _ := by simp
  rw [Finset.sum_add_distrib]
  linarith [tr.P3_card]

end KKContribution
