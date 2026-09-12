import Definitions.Def_TaoFivePrimes_Theorem51Scale
import examples.«five-primes».Theorem51ScaleCoefficients
import examples.«five-primes».Theorem51PaddedRectangle

namespace TaoFivePrimes
open Finset

theorem theorem51_scale_bound_positive (x alpha U V W : ℝ) (q : ℕ)
    (hq : 100 ≤ q) (hW : 40 ≤ W) (hxW : 40 ≤ x / W)
    (hlo : ((q : ℝ) - 1) / (q : ℝ) ^ 2 ≤ 4 * alpha)
    (hhi : 4 * alpha ≤ ((q : ℝ) + 1) / (q : ℝ) ^ 2) :
    ‖theorem51ScaleSum x alpha U V W‖ ≤
      (1.1 / 8) * Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) * Real.log W := by
  have hw : 0 < W := by linarith
  have hx : 0 ≤ x := by
    have hh := (le_div_iff₀ hw).mp hxW
    nlinarith
  have hq0 : 0 < q := by omega
  have hqr : (100 : ℝ) ≤ q := by exact_mod_cast hq
  let L : ℤ := ⌈(x / (2 * W) - 1) / 2⌉
  let R : ℤ := ⌊(x / W - 1) / 2⌋
  let M : ℕ := (q + 1) / 2
  let K : ℕ := (R - L).toNat / M + 1
  let D : ℝ := (oddHalfInterval (x / (2 * W)) (x / W)).card
  let N : ℝ := (oddRealInterval (W / 2) W).card
  let C : ℝ := (W / 4 + 2 * q) * (x / (2 * W * q) + 1)
  have hM : 0 < M := by dsimp [M]; omega
  have hb := unit_padded_odd_rectangle q alpha hqr hlo hhi L R
    ⌈(W / 2 - 1) / 2⌉ ⌊(W - 1) / 2⌋ K M
    (integer_block_cover L R M hM) (half_modulus_block_size q).2
    (scaleRowCoefficient V) (scaleColumnCoefficient U)
  change ‖theorem51ScaleSum x alpha U V W‖ ≤
    Real.sqrt ((K : ℝ) * ((N + 2 * q - 1) *
      (∑ n ∈ oddHalfInterval (x / (2 * W)) (x / W), ‖scaleColumnCoefficient U n‖ ^ 2)) *
      ∑ w ∈ oddRealInterval (W / 2) W, ‖scaleRowCoefficient V w‖ ^ 2) at hb
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hfactor : 0 ≤ N + 2 * q - 1 := by linarith
  have hk := scale_column_block_count x W q hw hx hq0
  change (K : ℝ) ≤ x / (2 * W * q) + 1 at hk
  have hn := scale_row_counts W hW
  have hc : (K : ℝ) * (N + 2 * q - 1) ≤ C := by
    have ht : N + 2 * q - 1 ≤ W / 4 + 2 * q := by linarith [hn.1]
    have hm := mul_le_mul hk ht hfactor (by positivity : 0 ≤ x / (2 * W * q) + 1)
    dsimp [C]
    nlinarith
  have hd := scale_column_energy (oddHalfInterval (x / (2 * W)) (x / W)) U
  have ha := scale_row_energy V W hW
  have he : (K : ℝ) * ((N + 2 * q - 1) *
      (∑ n ∈ oddHalfInterval (x / (2 * W)) (x / W), ‖scaleColumnCoefficient U n‖ ^ 2)) *
      (∑ w ∈ oddRealInterval (W / 2) W, ‖scaleRowCoefficient V w‖ ^ 2) ≤
      C * D * (N / 4 * Real.log W ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hd (mul_nonneg (Nat.cast_nonneg K) hfactor)
    have h2 := mul_le_mul_of_nonneg_right hc hD0
    have h3 := mul_le_mul (h1.trans h2) ha (sum_nonneg (fun _ _ => sq_nonneg _))
      (mul_nonneg hC0 hD0)
    convert h3 using 2 <;> first | rfl | ring
  exact hb.trans ((Real.sqrt_le_sqrt he).trans
    (typeII_counting_constant C x W D N hC0 hx hW hD0 hN0
      (scale_column_count x W hw hxW) hn.2))

end TaoFivePrimes






