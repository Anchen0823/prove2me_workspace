import Solutions.Sol_KKBinPacking_GeometricGrouping_alg2_step3_card_le

set_option autoImplicit false

open KKBinPacking.GeometricGrouping

namespace KKTelescopeAudit

/-- If `g > 1`, Step 1 removes every item of a valid instance. -/
lemma inst_zero_eq_zero_of_one_lt (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (hI : IsInstance I) (tr : Alg2Trace k g I) (hg : 1 < g) :
    tr.inst 0 = 0 := by
  rw [tr.inst_zero]
  apply Multiset.filter_eq_nil.mpr
  intro x hx
  have hxlt := (hI x hx).2
  simp only [not_lt]
  linarith

/-- A zero current instance has no rounded pairs, hence the next instance is empty. -/
lemma inst_succ_eq_zero_of_inst_eq_zero (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (tr : Alg2Trace k g I) (i : ℕ) (hi : i < tr.t)
    (hzero : tr.inst i = 0) :
    tr.inst (i + 1) = 0 := by
  have hpairs : geomPairs k (tr.inst i) = 0 := by
    rw [hzero]
    simp [geomPairs, geomGroups, geomGroupsList]
  have hsub := tr.Bp_sub i hi
  rw [hpairs] at hsub
  have hbp : (tr.Bp i).join = 0 := Multiset.le_zero.mp hsub
  rw [tr.inst_succ i hi, hzero, hpairs, hbp]
  simp

/-- Once Step 1 is empty, every state in the finite trace is empty. -/
lemma all_inst_eq_zero_of_one_lt (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (hI : IsInstance I) (tr : Alg2Trace k g I) (hg : 1 < g) :
    ∀ i ≤ tr.t, tr.inst i = 0 := by
  have hzero := inst_zero_eq_zero_of_one_lt k g I hI tr hg
  intro i
  induction i with
  | zero =>
      intro _
      exact hzero
  | succ i ih =>
      intro hi
      apply inst_succ_eq_zero_of_inst_eq_zero k g I tr i (by omega)
      exact ih (by omega)

/-- For any valid input, a trace with `g > 1` cannot execute the loop. -/
theorem trace_t_eq_zero_of_one_lt (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (hI : IsInstance I) (tr : Alg2Trace k g I) (hg : 1 < g) :
    tr.t = 0 := by
  by_contra ht
  have htpos : 1 ≤ tr.t := by omega
  have hall := all_inst_eq_zero_of_one_lt k g I hI tr hg
  have hzero0 := hall 0 (by omega)
  have hzerot := hall tr.t le_rfl
  have hexit := tr.loop_exit
  rw [hzerot, SIZE] at hexit
  have hrun := tr.loop_run 0 (by omega)
  rw [hzero0, SIZE] at hrun
  simp at hexit hrun
  linarith

/-- A trace that executes at least one iteration must have `g ≤ 1`. -/
theorem trace_g_le_one_of_t_pos (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I)
    (ht : 1 ≤ tr.t) :
    g ≤ 1 := by
  by_contra hnot
  have hg : 1 < g := lt_of_not_ge hnot
  have htzero := trace_t_eq_zero_of_one_lt k g I hI tr hg
  omega

/-- Every state through the exit is a valid instance: each residual piece is the first
component of a geometric pair from the previous instance. -/
theorem trace_inst_isInstance (k : ℕ) (g : ℝ) (I : Multiset ℝ)
    (hI : IsInstance I) (tr : Alg2Trace k g I) :
    ∀ i ≤ tr.t, IsInstance (tr.inst i) := by
  intro i
  induction i with
  | zero =>
      intro _ x hx
      rw [tr.inst_zero] at hx
      exact hI x (Multiset.mem_filter.mp hx).1
  | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hiter : i < tr.t := by omega
      rw [tr.inst_succ i hiter]
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
      have hpairs : p ∈ geomPairs k (tr.inst i) :=
        Multiset.mem_of_le (Multiset.sub_le_self _ _) hp
      exact hprev p.1 (KKContribution.fst_mem_source k (tr.inst i) hpairs)

/-- Each instance at the beginning of an executed iteration is nonempty. -/
theorem trace_inst_ne_zero_of_lt (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I)
    (i : ℕ) (hi : i < tr.t) :
    tr.inst i ≠ 0 := by
  have hg1 : g ≤ 1 := trace_g_le_one_of_t_pos k hk g hg0 I hI tr (by omega)
  have hlog : 0 ≤ Real.log (1 / g) := Real.log_nonneg (by
    exact (le_div_iff₀ hg0).2 hg1)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < 1 - 1 / (k : ℝ) := by
    have hlt : 1 / (k : ℝ) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    linarith
  have hcoeff : 0 ≤ 1 / (1 - 1 / (k : ℝ)) := by positivity
  have hthreshold : 1 ≤ alg2Threshold k g := by
    simp only [alg2Threshold]
    have := mul_nonneg hcoeff hlog
    linarith
  have hrun := tr.loop_run i hi
  have hsize : 0 < SIZE (tr.inst i) := lt_of_le_of_lt hthreshold hrun
  intro hzero
  rw [hzero, SIZE] at hsize
  norm_num at hsize

end KKTelescopeAudit
