import Solutions.SondowCutoffAlgebra
import Solutions.SondowPrefixSymmetry
import Solutions.SondowTripleReindex

open Finset

namespace EulerMascheroni.Sondow

theorem harmonic_interval_sum (a b : ℕ) (hab : a ≤ b) :
    (∑ j ∈ Icc (a+1) b, (1:ℝ)/j) = (harmonic b:ℝ)-(harmonic a:ℝ) := by
  have hI : Icc (a+1) b = Ico (a+1) (b+1) := by
    ext j
    simp only [mem_Icc, mem_Ico]
    omega
  have hs (m : ℕ) : (∑ j ∈ range (m+1), (1:ℝ)/j) = (harmonic m:ℝ) := by
    rw [sum_range_succ']
    simp only [Nat.cast_zero, div_zero, add_zero]
    simp only [harmonic]
    push_cast
    simp only [one_div]
  rw [hI, sum_Ico_eq_sub _ (by omega), hs, hs]

theorem shifted_log_interval (n i j : ℕ) :
    (∑ r ∈ range (j-i), Real.log (n+i+r+1:ℕ)) =
      ∑ k ∈ Icc (i+1) j, Real.log (n+k:ℕ) := by
  have hI : Icc (i+1) j = Ico (i+1) (j+1) := by
    ext k
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hI, sum_Ico_eq_sum_range, Nat.add_sub_add_right]
  apply sum_congr rfl
  intro r hr
  congr 2
  omega

theorem L_eq_harmonic_prefix (n : ℕ) :
    L n = 2*(∑ k ∈ Icc 1 n, (∑ i ∈ range k, harmonicRowWeight n i)*Real.log (n+k:ℕ)) := by
  unfold L
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk0 : 0 < k := (mem_Icc.mp hk).1
  have hkn : k ≤ n := (mem_Icc.mp hk).2
  rw [harmonic_prefix_min n k hk0 hkn]
  have hI : Icc 0 (min (k-1) (n-k)) = range (min (k-1) (n-k)+1) := by
    ext i
    simp only [mem_Icc, mem_range]
    omega
  rw [hI, sum_mul, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ min (k-1) (n-k) := by have := mem_range.mp hi; omega
  have hineq : i ≤ n-i := by have := (le_min_iff.mp hi'); omega
  calc
    _ = 2*(n.choose i:ℝ)^2*(∑ j ∈ Icc (i+1) (n-i), (1:ℝ)/j)*Real.log (n+k:ℕ) := by
      rw [mul_sum, sum_mul]
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [harmonic_interval_sum i (n-i) hineq]; unfold harmonicRowWeight; ring

theorem signedLogForm_eq_harmonic_prefix (n : ℕ) :
    signedLogForm n =
      2*(∑ k ∈ Icc 1 n, (∑ i ∈ range k, harmonicRowWeight n i)*Real.log (n+k:ℕ)) := by
  let c (i j : ℕ) : ℝ := (-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)
  have ht (i j : ℕ) : -(c i j/(j-i:ℕ)*(∑ r ∈ range (j-i), Real.log (n+i+r+1:ℕ))) =
      ∑ k ∈ Icc (i+1) j, -c i j/(j-i:ℕ)*Real.log (n+k:ℕ) := by
    rw [shifted_log_interval, mul_sum, ← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    ring
  calc
    _ = 2*(∑ j ∈ range (n+1), ∑ i ∈ range j,
        -(c i j/(j-i:ℕ)*(∑ r ∈ range (j-i), Real.log (n+i+r+1:ℕ)))) := by
      simp only [sum_neg_distrib, signedLogForm, c]
      ring
    _ = 2*(∑ k ∈ Icc 1 n, ∑ i ∈ range k, ∑ j ∈ Ico k (n+1),
        -c i j/(j-i:ℕ)*Real.log (n+k:ℕ)) := by
      simp_rw [ht]
      rw [triangle_interval_sum_reindex]
    _ = _ := by
      simp_rw [← sum_mul]
      congr 1
      apply sum_congr rfl
      intro k hk
      rw [show (∑ i ∈ range k, ∑ j ∈ Ico k (n+1), -c i j/(j-i:ℕ)) =
          ∑ i ∈ range k, harmonicRowWeight n i from
        binomial_rectangle_identity n k (by have := (mem_Icc.mp hk).2; omega)]

theorem signedLogForm_eq_L (n : ℕ) : signedLogForm n = L n := by
  rw [signedLogForm_eq_harmonic_prefix, L_eq_harmonic_prefix]

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.signedLogForm_eq_L
