import examples.«five-primes».Theorem51TypeIIAlgebra

namespace TaoFivePrimes

lemma sqrt_square_div_product (x a b : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    Real.sqrt (x ^ 2 / (a * b)) = x / (Real.sqrt a * Real.sqrt b) := by
  rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx, Real.sqrt_mul ha]

lemma sqrt_two_q_x (x q : ℝ) (hx : 0 < x) (hq : 0 < q) :
    Real.sqrt (2 * q * x) = Real.sqrt 2 * (x / Real.sqrt (x / q)) := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * q),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_div hx.le]
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hsq : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  field_simp
  nlinarith [Real.sq_sqrt hx.le]

lemma sqrt_eight : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
  norm_num

lemma typeII_radical_normalized (x q W : ℝ) (hx : 0 < x) (hq : 0 < q)
    (hW : 0 < W) (hregime : x ≤ q * W) :
    Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) ≤
      (1 / (2 * Real.sqrt 2) * (x / Real.sqrt q) +
        Real.sqrt 2 * (x / Real.sqrt (x / q))) +
      (Real.sqrt x / 2) * Real.sqrt W + (x / Real.sqrt 2) / Real.sqrt W := by
  have h := typeII_radical_unit x q W hx hq hW hregime
  rw [sqrt_square_div_product x 8 q hx.le (by norm_num), sqrt_eight,
    sqrt_square_div_product x 2 W hx.le (by norm_num), sqrt_two_q_x x q hx hq,
    Real.sqrt_div (mul_nonneg hx.le hW.le), Real.sqrt_mul hx.le] at h
  have hfour : Real.sqrt (4 : ℝ) = 2 := by norm_num
  rw [hfour] at h
  convert h using 1 <;> first | rfl | ring

lemma sqrt_scale_endpoint (x U : ℝ) (hx : 0 ≤ x) (hU : 0 < U) :
    Real.sqrt x * Real.sqrt (x / U) = x / Real.sqrt U := by
  rw [Real.sqrt_div hx, ← mul_div_assoc, Real.mul_self_sqrt hx]

end TaoFivePrimes


