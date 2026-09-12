import examples.«five-primes».Theorem51ScaleBound

namespace TaoFivePrimes
open Finset

lemma expCircle_neg_conjugate (t : ℝ) :
    expCircle (-t) = star (expCircle t) := by
  rw [expCircle, expCircle, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

lemma theorem51ScaleSum_neg (x alpha U V W : ℝ) :
    theorem51ScaleSum x (-alpha) U V W = star (theorem51ScaleSum x alpha U V W) := by
  unfold theorem51ScaleSum
  simp only [star_sum, star_mul, mul_comm]
  apply sum_congr rfl
  intro w hw
  have hr : star (scaleRowCoefficient V w) = scaleRowCoefficient V w := by
    unfold scaleRowCoefficient
    split_ifs <;> simp
  rw [hr]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hc : star (scaleColumnCoefficient U n) = scaleColumnCoefficient U n := by
    unfold scaleColumnCoefficient
    split_ifs <;> simp
  rw [hc, ← expCircle_neg_conjugate]
  congr 2
  ring

theorem theorem51_scale_bound_signed (x alpha beta U V W : ℝ) (a : ℤ) (q : ℕ)
    (hq : 100 ≤ q) (hW : 40 ≤ W) (hxW : 40 ≤ x / W)
    (ha : a.natAbs = 1) (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    ‖theorem51ScaleSum x alpha U V W‖ ≤
      (1.1 / 8) * Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) * Real.log W := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have he1 : 1 / (q : ℝ) - 1 / (q : ℝ) ^ 2 = ((q : ℝ) - 1) / (q : ℝ) ^ 2 := by
    field_simp <;> ring
  have he2 : 1 / (q : ℝ) + 1 / (q : ℝ) ^ 2 = ((q : ℝ) + 1) / (q : ℝ) ^ 2 := by
    field_simp <;> ring
  have hb := abs_le.mp hbeta
  have haa : a = 1 ∨ a = -1 := by omega
  rcases haa with rfl | rfl
  · simp only [Int.cast_one, Int.cast_neg, neg_div] at halpha
    apply theorem51_scale_bound_positive x alpha U V W q hq hW hxW
    · rw [← he1]; linarith
    · rw [← he2]; linarith
  · simp only [Int.cast_one, Int.cast_neg, neg_div] at halpha
    have hh := theorem51_scale_bound_positive x (-alpha) U V W q hq hW hxW
      (by rw [← he1]; linarith) (by rw [← he2]; linarith)
    simpa [theorem51ScaleSum_neg] using hh

end TaoFivePrimes


