import Solutions.SondowLogMoment
import Solutions.SondowFiniteSums

open MeasureTheory Finset

namespace EulerMascheroni.Sondow

/-- Evaluation of the diagonal in the finite geometric expansion. -/
theorem finite_diagonal_moments (m N : ℕ) :
    (∑ v ∈ range N, ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ (m+v) * y ^ (m+v) / (-Real.log (x*y))) =
      (harmonic (m+N):ℝ) - (harmonic m:ℝ) := by
  simp_rw [logarithmic_nat_moment_diagonal]
  simpa only [Nat.cast_add, Nat.cast_one] using harmonic_moment_sum m N

/-- Evaluation of an off-diagonal in the finite geometric expansion. -/
theorem finite_off_diagonal_moments (m N d : ℕ) (hd : 0 < d) :
    (∑ v ∈ range N, ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ (m+v) * y ^ (m+v+d) / (-Real.log (x*y))) =
      (∑ k ∈ range d, Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ))) / (d:ℝ) := by
  calc
    _ = ∑ v ∈ range N, Real.log ((m+v+d+1:ℕ)/(m+v+1:ℝ))/(d:ℝ) := by
      apply sum_congr rfl
      intro v hv
      rw [logarithmic_nat_moment_off_diagonal _ _ (by omega)]
      push_cast
      congr 1
      ring
    _ = _ := by rw [← sum_div, logarithmic_moment_sum]

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.finite_diagonal_moments
#print axioms EulerMascheroni.Sondow.finite_off_diagonal_moments
