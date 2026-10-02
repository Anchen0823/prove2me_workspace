namespace KKTelescope

lemma lin_nonneg (I : Multiset ℝ) : 0 ≤ LIN I := by
  apply Real.sInf_nonneg
  rintro z ⟨x, hx, rfl⟩
  exact Finset.sum_nonneg (fun c _ => hx.2.1 c)

lemma fractional_cost (x : Multiset ℝ →₀ ℝ) :
    (∑ c ∈ x.support, (x c - (⌊x c⌋₊ : ℝ))) = lpCost x - principalCount x := by
  simp [lpCost, principalCount, Finset.sum_sub_distrib, Nat.cast_sum]

end KKTelescope

theorem solution (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) :
    (∀ i < tr.t,
      LIN (tr.inst (i + 1)) ≤ LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ∧
        LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ≤
          LIN (tr.inst i) + 1 - principalCount (tr.x i)) ∧
    ((∑ i ∈ Finset.range tr.t, principalCount (tr.x i) : ℕ) : ℝ) ≤
      LIN (geomJ k (tr.inst 0)) + tr.t := by
  classical
  have hstep : ∀ i < tr.t,
      LIN (tr.inst (i + 1)) ≤ LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ∧
        LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ≤
          LIN (tr.inst i) + 1 - principalCount (tr.x i) := by
    intro i hi
    have hg1 := KKTelescopeAudit.trace_g_le_one_of_t_pos k hk g hg0 I hI tr (by omega)
    have hinst := KKTelescopeAudit.trace_inst_isInstance k g I hI tr i (by omega)
    have hne := KKTelescopeAudit.trace_inst_ne_zero_of_lt k hk g hg0 I hI tr i hi
    have hrec := (alg2_size_recursion k hk g hg0 hg1 I hI tr i hi).2.1
    rw [KKTelescope.fractional_cost] at hrec
    have hcost := tr.x_cost i hi
    have hmono := (geomGroup_bounds (tr.inst i) hinst hne k hk).2.1.1
    constructor <;> linarith
  refine ⟨hstep, ?_⟩
  by_cases ht : tr.t = 0
  · simp only [ht, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, add_zero]
    exact KKTelescope.lin_nonneg _
  have hsum : ∀ n, 1 ≤ n → n ≤ tr.t →
      ((∑ i ∈ Finset.range n, principalCount (tr.x i) : ℕ) : ℝ) + LIN (tr.inst n) ≤
        LIN (geomJ k (tr.inst 0)) + n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn hnt
      by_cases hn0 : n = 0
      · subst n
        have hs := (hstep 0 (by omega)).1
        simpa using
          (show (principalCount (tr.x 0) : ℝ) + LIN (tr.inst 1) ≤
            LIN (geomJ k (tr.inst 0)) + 1 by linarith)
      · have hprev := ih (by omega) (by omega)
        have hs := (hstep n (by omega)).1.trans (hstep n (by omega)).2
        rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_add, Nat.cast_one]
        linarith
  have hs := hsum tr.t (by omega) le_rfl
  have hn := KKTelescope.lin_nonneg (tr.inst tr.t)
  linarith
