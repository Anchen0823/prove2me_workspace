import Solutions.SondowFiniteEvaluation
import Solutions.SondowBinomialCoefficients
import Mathlib.Algebra.BigOperators.Intervals

open Finset

namespace EulerMascheroni.Sondow

theorem triangular_sum_reindex (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range (n+1), ∑ i ∈ range j, f i j) =
      ∑ i ∈ range (n+1), ∑ j ∈ Icc (i+1) n, f i j := by
  have hI (i : ℕ) : Ico (i+1) (n+1) = Icc (i+1) n := by
    ext k
    simp only [mem_Ico, mem_Icc]
    omega
  simpa only [Nat.Ico_zero_eq_range, hI] using
    (sum_Ico_Ico_comm' 0 (n+1) f).symm

theorem range_sum_shift_one (f : ℕ → ℝ) (d : ℕ) :
    (∑ k ∈ range d, f (k+1)) = ∑ k ∈ Icc 1 d, f k := by
  have hI : Icc 1 d = Ico 1 (d+1) := by
    ext k
    simp only [mem_Ico, mem_Icc]
    omega
  rw [hI, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

theorem boundary_log_split (m N d : ℕ) (hN : 0 < N) :
    (∑ k ∈ range d, Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ))) =
      (d:ℝ)*Real.log N - (∑ k ∈ range d, Real.log (m+k+1:ℕ)) +
        ∑ k ∈ range d, Real.log (1+(m+k+1:ℕ)/(N:ℝ)) := by
  have he (k : ℕ) : Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ)) =
      Real.log N - Real.log (m+k+1:ℕ) + Real.log (1+(m+k+1:ℕ)/(N:ℝ)) := by
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    rw [Real.log_div (by positivity) (by positivity)]
    have hnum : (m+N+k+1:ℕ) = (N:ℝ)*(1+(m+k+1:ℕ)/(N:ℝ)) := by
      push_cast
      field_simp
      ring
    rw [hnum, Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  simp_rw [he, sum_add_distrib, sum_sub_distrib]
  simp

noncomputable def signedLogForm (n : ℕ) : ℝ :=
  -2 * ∑ j ∈ range (n+1), ∑ i ∈ range j,
    ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ) *
      ∑ k ∈ range (j-i), Real.log (n+i+k+1:ℕ)

theorem diagonal_cutoff_split (n N : ℕ) :
    (∑ i ∈ range (n+1), (n.choose i:ℝ)^2 *
      ((harmonic (n+i+N):ℝ)-(harmonic (n+i):ℝ))) =
      ((2*n).choose n:ℝ)*(harmonic N:ℝ) - (A n:ℝ) +
        ∑ i ∈ range (n+1), (n.choose i:ℝ)^2 *
          ((harmonic (N+n+i):ℝ)-(harmonic N:ℝ)) := by
  have hA : (A n:ℝ) = ∑ i ∈ range (n+1), (n.choose i:ℝ)^2*(harmonic (n+i):ℝ) := by
    simp only [A]
    push_cast
    rfl
  rw [hA, ← choose_square_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  rw [show n+i+N = N+n+i by omega]
  ring

theorem weighted_boundary_log_split (m N d : ℕ) (hN : 0 < N) (hd : 0 < d) (c : ℝ) :
    c/(d:ℝ) * (∑ k ∈ range d, Real.log ((m+N+k+1:ℕ)/(m+k+1:ℝ))) =
      c*Real.log N - c/(d:ℝ)*(∑ k ∈ range d, Real.log (m+k+1:ℕ)) +
        c/(d:ℝ)*(∑ k ∈ range d, Real.log (1+(m+k+1:ℕ)/(N:ℝ))) := by
  rw [boundary_log_split m N d hN]
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem correction_triangle_eq (n N : ℕ) :
    (∑ j ∈ range (n+1), ∑ i ∈ range j,
      ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ) *
        ∑ k ∈ range (j-i), Real.log (1+(n+i+k+1:ℕ)/(N:ℝ))) =
      ∑ i ∈ range (n+1), ∑ j ∈ Icc (i+1) n,
        ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ) *
          ∑ k ∈ Icc 1 (j-i), Real.log (1+(n+i+k:ℕ)/(N:ℝ)) := by
  rw [triangular_sum_reindex]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  congr 1
  simpa only [Nat.add_assoc] using range_sum_shift_one
    (fun k => Real.log (1+(n+i+k:ℕ)/(N:ℝ))) (j-i)

/-- Complete finite cutoff identity with the signed logarithmic form.
Identifying signedLogForm with L is the remaining combinatorial step. -/
theorem finite_cutoff_signed_identity (n N : ℕ) (hn : 0 < n) (hN : 0 < N) :
    I n - remainder n N = ((2*n).choose n:ℝ) *
      ((harmonic N:ℝ)-Real.log N) + signedLogForm n - (A n:ℝ) + cutoffError n N := by
  let c (i j : ℕ) : ℝ := (-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)
  let B (i j : ℕ) : ℝ := ∑ k ∈ range (j-i), Real.log (n+i+k+1:ℕ)
  let E (i j : ℕ) : ℝ := ∑ k ∈ range (j-i), Real.log (1+(n+i+k+1:ℕ)/(N:ℝ))
  have hcoeff : 2*(∑ j ∈ range (n+1), ∑ i ∈ range j, c i j) =
      -((2*n).choose n:ℝ) := signed_triangular_choose_sum n hn
  have hL : signedLogForm n = -2*(∑ j ∈ range (n+1), ∑ i ∈ range j,
      c i j/(j-i:ℕ)*B i j) := rfl
  have hoff : 2*(∑ j ∈ range (n+1), ∑ i ∈ range j,
      c i j/(j-i:ℕ)*(∑ k ∈ range (j-i), Real.log ((n+i+N+k+1:ℕ)/(n+i+k+1:ℝ)))) =
      -((2*n).choose n:ℝ)*Real.log N + signedLogForm n +
        2*(∑ j ∈ range (n+1), ∑ i ∈ range j, c i j/(j-i:ℕ)*E i j) := by
    calc
      _ = 2*(∑ j ∈ range (n+1), ∑ i ∈ range j,
          (c i j*Real.log N-c i j/(j-i:ℕ)*B i j+c i j/(j-i:ℕ)*E i j)) := by
        congr 1
        apply sum_congr rfl
        intro j hj
        apply sum_congr rfl
        intro i hi
        have hij : i < j := mem_range.mp hi
        simpa only [B, E, Nat.cast_add] using
          weighted_boundary_log_split (n+i) N (j-i) hN (by omega) (c i j)
      _ = _ := by
        simp_rw [sum_add_distrib, sum_sub_distrib, ← sum_mul]
        rw [hL]
        nlinarith [congrArg (fun z : ℝ => z*Real.log N) hcoeff]
  rw [finite_cutoff_evaluation n N hn, diagonal_cutoff_split]
  change _ + 2*(∑ j ∈ range (n+1), ∑ i ∈ range j,
    c i j/(j-i:ℕ)*(∑ k ∈ range (j-i), Real.log ((n+i+N+k+1:ℕ)/(n+i+k+1:ℝ)))) = _
  rw [hoff]
  unfold cutoffError
  rw [← correction_triangle_eq]
  dsimp only [c, E]
  ring

/-- Exact original finite-cutoff statement, conditional only on the logarithmic-form identity. -/
theorem finite_cutoff_identity_of_logarithmic_forms_equal (n N : ℕ)
    (hn : 0 < n) (hN : 0 < N) (hL : signedLogForm n = L n) :
    I n - remainder n N = ((2*n).choose n:ℝ) *
      ((harmonic N:ℝ)-Real.log N) + L n - (A n:ℝ) + cutoffError n N := by
  simpa only [hL] using finite_cutoff_signed_identity n N hn hN

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.boundary_log_split
#print axioms EulerMascheroni.Sondow.diagonal_cutoff_split
#print axioms EulerMascheroni.Sondow.finite_cutoff_signed_identity
#print axioms EulerMascheroni.Sondow.finite_cutoff_identity_of_logarithmic_forms_equal
