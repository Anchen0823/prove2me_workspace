import Definitions.Def_eulerMascheroni_sondow
import Mathlib.Tactic

open EulerMascheroni.Sondow Finset

theorem solution (integral_identity : ∀ (n : ℕ) (hn : 0 < n), I n = ((2*n).choose n : ℝ) * Real.eulerMascheroniConstant + L n - (A n : ℝ))
(scaled_integral_bounds : ∀ (n : ℕ) (hn : 0 < n), 0 < (d (2*n) : ℝ) * I n ∧ (d (2*n) : ℝ) * I n < (1/2 : ℝ)^n)
(scaled_A_integral : ∀ (n : ℕ), ∃ z : ℤ, (d (2*n) : ℝ) * (A n : ℝ) = z)
(fractional_lower_bound_conjecture : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
      (1/2 : ℝ)^n ≤ Int.fract ((d (2*n) : ℝ) * L n)) : Irrational Real.eulerMascheroniConstant := by
  intro ⟨r, hr⟩
  obtain ⟨n, hn, hpos, hfrac⟩ := fractional_lower_bound_conjecture r.den
  have hd : r.den ∣ d (2*n) := Finset.dvd_lcm (f := id)
    (by simp only [mem_Icc]; exact ⟨r.den_pos, by omega⟩)
  obtain ⟨k, hk⟩ := hd
  obtain ⟨z, hz⟩ := scaled_A_integral n
  have hrat : (d (2*n) : ℝ) * ((2*n).choose n : ℝ) * Real.eulerMascheroniConstant =
      (((k : ℤ) * ((2*n).choose n : ℤ) * r.num : ℤ) : ℝ) := by
    rw [← hr, Rat.cast_def, hk]
    push_cast
    field_simp
  have hid := integral_identity n hpos
  push_cast at hrat
  have heq : (d (2*n) : ℝ) * L n = (d (2*n) : ℝ) * I n +
      ((z - (k : ℤ) * ((2*n).choose n : ℤ) * r.num : ℤ) : ℝ) := by
    push_cast
    have hscaled := congrArg (fun t : ℝ => (d (2*n) : ℝ) * t) hid
    nlinarith
  obtain ⟨hlo, hhi⟩ := scaled_integral_bounds n hpos
  have hunit : (d (2*n) : ℝ) * I n < 1 :=
    lt_of_lt_of_le hhi (pow_le_one₀ (by norm_num) (by norm_num))
  rw [heq, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨hlo.le, hunit⟩] at hfrac
  exact (not_lt_of_ge hfrac) hhi

#print axioms solution

