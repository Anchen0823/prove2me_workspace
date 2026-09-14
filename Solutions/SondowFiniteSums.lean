import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Finset

namespace EulerMascheroni.Sondow

/-- Diagonal moment summation, including the empty cutoff. -/
theorem harmonic_moment_sum (m N : ℕ) :
    (∑ v ∈ range N, (1:ℝ)/(m+v+1:ℕ)) =
      (harmonic (m+N):ℝ) - (harmonic m:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, show m+(N+1) = (m+N)+1 by omega, harmonic_succ]
    push_cast
    ring

/-- Discrete rectangle telescoping: sum the same boundary in the two directions. -/
theorem rectangular_sum_difference (f : ℕ → ℝ) (N d : ℕ) :
    (∑ v ∈ range N, (f (v+d)-f v)) =
      ∑ k ∈ range d, (f (N+k)-f k) := by
  have h1 := sum_range_add f N d
  have h2 := sum_range_add f d N
  rw [Nat.add_comm d N] at h2
  simp_rw [sum_sub_distrib]
  have he : (∑ v ∈ range N, f (d+v)) = ∑ v ∈ range N, f (v+d) := by
    apply sum_congr rfl
    intro v hv
    rw [Nat.add_comm]
  rw [he] at h2
  linarith

/-- Off-diagonal moments telescope to the short boundary logarithmic sum. -/
theorem logarithmic_moment_sum (m N d : ℕ) :
    (∑ v ∈ range N, Real.log ((m+v+d+1:ℕ)/(m+v+1:ℝ))) =
      ∑ k ∈ range d, Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ)) := by
  have he := rectangular_sum_difference (fun v => Real.log (m+v+1:ℕ)) N d
  have hl (v : ℕ) :
      Real.log ((m+v+d+1:ℕ)/(m+v+1:ℝ)) =
        Real.log (m+(v+d)+1:ℕ) - Real.log (m+v+1:ℕ) := by
    rw [Real.log_div (by positivity) (by positivity)]
    push_cast
    congr 1; congr 1; ring
  have hr (k : ℕ) :
      Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ)) =
        Real.log (m+(N+k)+1:ℕ) - Real.log (m+k+1:ℕ) := by
    rw [Real.log_div (by positivity) (by positivity)]
    push_cast
    congr 1; congr 1; ring
  simp_rw [hl, hr]
  exact he

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.harmonic_moment_sum
#print axioms EulerMascheroni.Sondow.rectangular_sum_difference
#print axioms EulerMascheroni.Sondow.logarithmic_moment_sum
