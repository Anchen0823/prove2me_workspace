import Solutions.SondowTruncatedIntegral
import Solutions.SondowFiniteMoments
import Solutions.SondowSymmetricSums

open MeasureTheory Finset

namespace EulerMascheroni.Sondow

theorem nat_moment_symmetric (a b : ℕ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, x^a*y^b/(-Real.log (x*y))) =
      ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, x^b*y^a/(-Real.log (x*y)) := by
  simp_rw [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  rw [integral_integral_swap (f := fun x y : ℝ => x^a*y^b/(-Real.log (x*y)))
    (nat_moment_integrable a b)]
  congr 1
  funext x
  congr 1
  funext y
  rw [mul_comm y x, mul_comm (y^a) (x^b)]

/-- The truncated integral evaluated into harmonic numbers and finite logarithmic sums.
The remaining identification with L is a finite combinatorial identity. -/
theorem finite_cutoff_evaluation (n N : ℕ) (hn : 0 < n) :
    I n - remainder n N =
      (∑ i ∈ range (n+1), (n.choose i:ℝ)^2 *
        ((harmonic (n+i+N):ℝ)-(harmonic (n+i):ℝ))) +
      2 * ∑ j ∈ range (n+1), ∑ i ∈ range j,
        ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ) *
          ∑ k ∈ range (j-i), Real.log ((n+i+N+k+1:ℕ)/(n+i+k+1:ℝ)) := by
  let F (i j : ℕ) : ℝ :=
    ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) *
      ∑ v ∈ range N, ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
        x^(n+i+v)*y^(n+j+v)/(-Real.log (x*y))
  have hsymm (i j : ℕ) : F i j = F j i := by
    dsimp only [F]
    have he : (∑ v ∈ range N, ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
        x^(n+i+v)*y^(n+j+v)/(-Real.log (x*y))) =
      ∑ v ∈ range N, ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
        x^(n+j+v)*y^(n+i+v)/(-Real.log (x*y)) := by
      apply sum_congr rfl
      intro v hv
      exact nat_moment_symmetric _ _
    rw [he, Nat.add_comm i j]
    ring
  have hexp : I n - remainder n N = ∑ i ∈ range (n+1), ∑ j ∈ range (n+1), F i j := by
    rw [truncated_integral_moment_expansion n N hn]
    simp only [F, mul_sum]
  rw [hexp, symmetric_square_sum F hsymm]
  congr 1
  · apply sum_congr rfl
    intro i hi
    dsimp only [F]
    rw [finite_diagonal_moments]
    have hsign : (-1:ℝ)^(i+i) = 1 := by
      rw [← two_mul i, pow_mul]
      norm_num
    rw [hsign]
    ring
  · congr 1
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro i hi
    have hij : i < j := mem_range.mp hi
    dsimp only [F]
    have hindex (v : ℕ) : n+j+v = (n+i)+v+(j-i) := by omega
    simp_rw [hindex]
    rw [finite_off_diagonal_moments (n+i) N (j-i) (by omega)]
    push_cast
    ring

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.finite_cutoff_evaluation
