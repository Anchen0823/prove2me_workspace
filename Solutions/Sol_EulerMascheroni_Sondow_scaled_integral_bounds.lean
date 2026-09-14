import Theorems.Thm_EulerMascheroni_Sondow_integral_bounds
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_psi_bound
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

open EulerMascheroni.Sondow
open scoped ArithmeticFunction.vonMangoldt

private lemma lcm_lt_eight_pow (n : ℕ) (hn : 0 < n) : (d (2*n) : ℝ) < 8^n := by
  have hpsi := TaoFivePrimes.rosser_schoenfeld_psi_bound (2*n) (by omega)
  have heq : Chebyshev.psi (2*n : ℕ) =
      ∑ k ∈ Finset.range (2*n+1), (Λ k : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    congr 1
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [← heq, Chebyshev.psi_eq_log_lcmUpto] at hpsi
  have hd : (0:ℝ) < d (2*n) := by exact_mod_cast Nat.lcmUpto_pos (2*n)
  apply (Real.log_lt_log_iff hd (by positivity)).mp
  have hl8 : Real.log 8 = 3*Real.log 2 := by
    rw [show (8:ℝ)=2^3 by norm_num, Real.log_pow]; norm_num
  rw [Real.log_pow, hl8]
  have hlog := Real.log_two_gt_d9
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  change Real.log (d (2*n) : ℝ) < _ at hpsi
  push_cast at hpsi
  nlinarith [mul_pos hnR (show 0 < 3*Real.log 2-2*1.03883 by linarith)]

theorem solution (n : ℕ) (hn : 0 < n) :
    0 < (d (2*n) : ℝ) * I n ∧ (d (2*n) : ℝ) * I n < (1/2:ℝ)^n := by
  obtain ⟨hp, hu⟩ := integral_bounds n hn
  have hd : (0:ℝ) < d (2*n) := by exact_mod_cast Nat.lcmUpto_pos (2*n)
  refine ⟨mul_pos hd hp, ?_⟩
  calc
    (d (2*n) : ℝ)*I n < (8:ℝ)^n*(1/16:ℝ)^n :=
      mul_lt_mul (lcm_lt_eight_pow n hn) hu.le hp (by positivity)
    _ = (1/2:ℝ)^n := by rw [← mul_pow]; norm_num

#print axioms solution
