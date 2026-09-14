import Mathlib.NumberTheory.Chebyshev
import Solutions.SondowSchoenfeldThreshold
import Solutions.SondowSchoenfeldThreeRows
import Solutions.SondowSchoenfeldTailNumeric

/-! The bounded logarithmic range of the RS1975 argument, using three rows.
The three analytic estimates remain explicit hypotheses; this is not an
unconditional proof of the Schoenfeld estimate. -/

namespace EulerMascheroni.Sondow

/-- Equation (3.19), with `t = log x`. This definition asserts no prime estimate. -/
noncomputable def schoenfeld1975Epsilon (t : ℝ) : ℝ :=
  let X := Real.sqrt (t / 9.645908801)
  0.257634 * (1 + 0.96642 / X) * X ^ (3 / 4 : ℝ) * Real.exp (-X)

theorem psi_error_of_three_table_rows (y : ℝ)
    (hy : (10 : ℝ) ^ 8 ≤ y) (hupper : Real.log y ≤ 1300)
    (h18 : 18.42 ≤ Real.log y →
      |Chebyshev.psi y - y| ≤ 0.0012015 * y)
    (h20 : 20 ≤ Real.log y →
      |Chebyshev.psi y - y| ≤ 0.00065941 * y)
    (h35 : 35 ≤ Real.log y →
      |Chebyshev.psi y - y| ≤ 0.000018315 * y) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by
  have hstart := log_ge_table_start y hy
  apply sondow_schoenfeld_three_rows hstart hupper (by linarith [hy])
  · intro _
    exact h18 hstart
  · intro h _
    exact h20 h
  · exact h35

theorem psi_error_of_rs1975_tail (y : ℝ) (hy : 0 < y)
    (ht : 1300 ≤ Real.log y)
    (hformula : |Chebyshev.psi y - y| ≤ y * schoenfeld1975Epsilon (Real.log y)) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by
  have hlog : 0 < Real.log y := by linarith
  have hn : schoenfeld1975Epsilon (Real.log y) * Real.log y < 0.025 := by
    simpa [schoenfeld1975Epsilon] using
      sondow_schoenfeld_tail_numeric (Real.log y) ht
  apply le_of_lt
  apply (lt_div_iff₀ (show 0 < 40 * Real.log y by positivity)).2
  calc
    |Chebyshev.psi y - y| * (40 * Real.log y)
        ≤ (y * schoenfeld1975Epsilon (Real.log y)) * (40 * Real.log y) :=
      mul_le_mul_of_nonneg_right hformula (by positivity)
    _ = (40 * y) * (schoenfeld1975Epsilon (Real.log y) * Real.log y) := by ring
    _ < (40 * y) * 0.025 := mul_lt_mul_of_pos_left hn (by positivity)
    _ = y := by ring

/-- The original error bound follows from three table estimates and Theorem 2.
All four analytic estimates remain explicit and unproved hypotheses here. -/
theorem psi_error_of_rs1975_estimates (y : ℝ) (hy : (10 : ℝ) ^ 8 ≤ y)
    (h18 : 18.42 ≤ Real.log y →
      |Chebyshev.psi y - y| ≤ 0.0012015 * y)
    (h20 : 20 ≤ Real.log y →
      |Chebyshev.psi y - y| ≤ 0.00065941 * y)
    (h35 : 35 ≤ Real.log y →
      |Chebyshev.psi y - y| ≤ 0.000018315 * y)
    (hformula : 1300 ≤ Real.log y →
      |Chebyshev.psi y - y| ≤ y * schoenfeld1975Epsilon (Real.log y)) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by
  rcases le_total (Real.log y) 1300 with hm | ht
  · exact psi_error_of_three_table_rows y hy hm h18 h20 h35
  · exact psi_error_of_rs1975_tail y (by linarith [hy]) ht (hformula ht)

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.psi_error_of_three_table_rows
#print axioms EulerMascheroni.Sondow.psi_error_of_rs1975_tail
#print axioms EulerMascheroni.Sondow.psi_error_of_rs1975_estimates
