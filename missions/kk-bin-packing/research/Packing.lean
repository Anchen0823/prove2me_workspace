import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2

open KKBinPacking.Shared KKBinPacking.GeometricGrouping

namespace KKContribution

lemma submultiset_sum_le {a b : Multiset ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ b, 0 ≤ x) : a.sum ≤ b.sum := by
  obtain ⟨c, rfl⟩ := Multiset.le_iff_exists_add.mp hab
  have hc : 0 ≤ c.sum := Multiset.sum_nonneg (fun x hx => hb x (by simp [hx]))
  simpa only [Multiset.sum_add] using (le_add_of_nonneg_right hc : a.sum ≤ a.sum + c.sum)

lemma principal_mem_configuration {J : Multiset ℝ} {x : Multiset ℝ →₀ ℝ}
    (hx : IsBasicFeasible J x) {c : Multiset ℝ} (hc : c ∈ principalConfigs x) :
    IsConfiguration J c := by
  classical
  obtain ⟨d, hd, hcd⟩ := Multiset.mem_sum.mp hc
  have hcd' : c = d := Multiset.eq_of_mem_replicate hcd
  subst c
  exact hx.1.1 d hd

lemma step3_packing (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (hI : IsInstance I) (tr : Alg2Trace k g I)
    (hpartition : ∀ J : Multiset ℝ, (geomPairs k J).map Prod.fst + geomJ' k J = J)
    (hround : ∀ (J : Multiset ℝ) p, p ∈ geomPairs k J → p.1 ≤ p.2) :
    IsPacking (I.filter (fun p => g < p)) (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) := by
  classical
  have hfst : ∀ (J : Multiset ℝ), (geomPairs k J).map Prod.fst ≤ J := by
    intro J
    calc
      _ ≤ (geomPairs k J).map Prod.fst + geomJ' k J := le_self_add
      _ = J := hpartition J
  have hstep : ∀ i < tr.t,
      ((tr.Bp i).map (Multiset.map Prod.fst) + tr.PJ' i).join + tr.inst (i + 1) =
        tr.inst i := by
    intro i hi
    rw [Multiset.join_add, ← Multiset.map_join, (tr.PJ'_packing i hi).1,
      tr.inst_succ i hi]
    calc
      (tr.Bp i).join.map Prod.fst + geomJ' k (tr.inst i) +
          (geomPairs k (tr.inst i) - (tr.Bp i).join).map Prod.fst =
          ((geomPairs k (tr.inst i) - (tr.Bp i).join) + (tr.Bp i).join).map Prod.fst +
            geomJ' k (tr.inst i) := by simp [Multiset.map_add, add_comm, add_left_comm]
      _ = tr.inst i := by rw [Multiset.sub_add_cancel (tr.Bp_sub i hi), hpartition]
  have hinst : ∀ i, i ≤ tr.t → ∀ p ∈ tr.inst i, 0 ≤ p := by
    intro i
    induction i with
    | zero =>
      intro hi p hp
      rw [tr.inst_zero] at hp
      exact (hI p (Multiset.mem_filter.mp hp).1).1.le
    | succ i ih =>
      intro hi p hp
      apply ih (by omega) p
      rw [← hstep i (by omega)]
      exact Multiset.mem_add.mpr (Or.inr hp)
  have hbins : ∀ i < tr.t, ∀ b ∈ (tr.Bp i).map (Multiset.map Prod.fst) + tr.PJ' i,
      b.sum ≤ 1 := by
    intro i hi b hb
    rcases Multiset.mem_add.mp hb with hb | hb
    · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
      obtain ⟨c, hc, hac⟩ := Multiset.exists_mem_of_rel_of_mem (tr.Bp_config i hi) ha
      have hconf := principal_mem_configuration (tr.x_basic i hi) hc
      have hpairs : ∀ p ∈ a, p ∈ geomPairs k (tr.inst i) := by
        intro p hp
        exact Multiset.mem_of_le (tr.Bp_sub i hi) (Multiset.mem_join.mpr ⟨a, ha, hp⟩)
      have hnonneg : ∀ s ∈ c, 0 ≤ s := by
        intro s hs
        obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp (hconf.2.1 s hs)
        exact (hinst i (by omega) p.1
          (Multiset.mem_of_le (hfst _) (Multiset.mem_map.mpr ⟨p, hp, rfl⟩))).trans
            (hround _ p hp)
      exact (Multiset.sum_map_le_sum_map Prod.fst Prod.snd
        (fun p hp => hround _ p (hpairs p hp))).trans
          ((submultiset_sum_le hac hnonneg).trans hconf.2.2)
    · exact (tr.PJ'_packing i hi).2 b hb
  have htelescope : ∀ n, n ≤ tr.t →
      (∑ i ∈ Finset.range n, ((tr.Bp i).map (Multiset.map Prod.fst) + tr.PJ' i)).join +
        tr.inst n = tr.inst 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ, Multiset.join_add, add_assoc, hstep n (by omega)]
      exact ih (by omega)
  constructor
  · unfold alg2Step3Bins
    rw [Multiset.join_add, tr.P3_packing.1, htelescope _ le_rfl, tr.inst_zero]
  · intro b hb
    rcases Multiset.mem_add.mp hb with hb | hb
    · obtain ⟨i, hi, hb⟩ := Multiset.mem_sum.mp hb
      exact hbins i (Finset.mem_range.mp hi) b hb
    · exact tr.P3_packing.2 b hb

end KKContribution

