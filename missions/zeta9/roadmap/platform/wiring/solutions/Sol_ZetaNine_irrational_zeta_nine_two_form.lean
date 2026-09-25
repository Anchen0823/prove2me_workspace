import Mathlib
import Theorems.Thm_ZetaNine_irrational_of_two_small_integer_forms
import Theorems.Thm_ZetaNine_exponentially_small_independent_forms_of_zeta_nine

open Filter
open scoped Topology

theorem solution : Irrational ((riemannZeta (9 : ℂ)).re) := by
  apply ZetaNine.irrational_of_two_small_integer_forms
  intro ε hε
  obtain ⟨c, hcpos, hc⟩ := ZetaNine.exponentially_small_independent_forms_of_zeta_nine
  have hlt1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have htend : Tendsto (fun n : ℕ => (Real.exp (-c)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-c)).le hlt1
  have hev : ∀ᶠ n : ℕ in atTop, (Real.exp (-c)) ^ n < ε :=
    (tendsto_order.1 htend).2 ε hε
  obtain ⟨n, hnε, b₁, a₁, b₂, a₂, hind, hs₁, hs₂⟩ := (hev.and hc).exists
  have hexp : Real.exp (-(c * (n : ℝ))) = (Real.exp (-c)) ^ n := by
    rw [show -(c * (n : ℝ)) = (n : ℝ) * (-c) by ring, Real.exp_nat_mul]
  exact ⟨b₁, a₁, b₂, a₂, hind, (hs₁.trans_eq hexp).trans hnε,
    (hs₂.trans_eq hexp).trans hnε⟩
