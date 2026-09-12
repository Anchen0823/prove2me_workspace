import examples.«five-primes».Theorem51ScaleIntegralBridge
import examples.«five-primes».Theorem51RootNormalization
import examples.«five-primes».Theorem51IntegratedMajorant

namespace TaoFivePrimes
open MeasureTheory

theorem theorem51_typeII_of_scale_bound
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ)
    (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q) (haunit : a.natAbs = 1)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hUVq : U * V < (q : ℝ) - 1)
    (hscale : ∀ W : ℝ, V ≤ W → W ≤ x / U →
      ‖TaoFivePrimes.theorem51ScaleSum x alpha U V W‖ ≤
        (1.1 / 8) * Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) * Real.log W) :
    TaoFivePrimes.theorem51TypeII x alpha U V ≤
      (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt (x / q))) *
        Real.log (x / (U * V)) * Real.log (V * x / U) +
      (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) *
        Real.log (x / U) := by
  have hu : 0 < U := by linarith
  have hv : 0 < V := by linarith
  have hx : 0 < x := by linarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hU1 : 1 ≤ U := by linarith
  have hV1 : 1 ≤ V := by linarith
  have huv : U * V ≤ x := by linarith
  have hVU : V ≤ x / U := (le_div_iff₀ hu).mpr (by nlinarith)
  let A := 1 / (2 * Real.sqrt 2) * (x / Real.sqrt q) + Real.sqrt 2 * (x / Real.sqrt (x / q))
  let B := Real.sqrt x / 2
  let C := x / Real.sqrt 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (W : ℝ) (hW : W ∈ Set.Icc V (x / U)) :
      ‖theorem51ScaleSum x alpha U V W‖ / W ≤ (1.1 / 8) * typeIIIntegralMajorant A B C W := by
    have hw : 0 < W := hv.trans_le hW.1
    have hl : 0 ≤ Real.log W := Real.log_nonneg (hV1.trans hW.1)
    have hregime := unit_regime_x_le_q_mul_W x U V q W hu.le hv.le hUVq hUV2 hW.1
    have hr := typeII_radical_normalized x q W hx hqr hw hregime
    change Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) ≤
      A + B * Real.sqrt W + C / Real.sqrt W at hr
    calc
      _ ≤ ((1.1 / 8) * Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) * Real.log W) / W :=
        div_le_div_of_nonneg_right (hscale W hW.1 hW.2) hw.le
      _ ≤ ((1.1 / 8) * (A + B * Real.sqrt W + C / Real.sqrt W) * Real.log W) / W := by
        gcongr
      _ = _ := by rw [← typeII_majorant_normalization A B C W hw]; ring
  have hi := theorem51_scale_weight_integrable x alpha U V hx hU1 hV1 huv
  have hj := (typeII_majorant_integrable V (x / U) A B C hv hVU).const_mul (1.1 / 8)
  have hm := intervalIntegral.integral_mono_on hVU hi hj hpoint
  have hint := typeII_majorant_integral_bound V (x / U) A B C hV1 hVU hB hC
  have hbound : theorem51TypeII x alpha U V ≤ (1.1 / 2) *
      ((A / 2) * Real.log ((x / U) / V) * Real.log (V * (x / U)) +
        2 * (B * Real.sqrt (x / U) + C / Real.sqrt V) * Real.log (x / U)) := by
    have hb := theorem51TypeII_le_scale_integral x alpha U V hx hU1 hV1 huv
    rw [intervalIntegral.integral_const_mul] at hm
    have hc := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4)
    have hd := mul_le_mul_of_nonneg_left hint (by norm_num : (0 : ℝ) ≤ 1.1 / 2)
    nlinarith
  have hratio : (x / U) / V = x / (U * V) := by ring
  have hprod : V * (x / U) = V * x / U := by ring
  have hBend : B * Real.sqrt (x / U) = (1 / 2) * (x / Real.sqrt U) := by
    dsimp [B]
    calc
      _ = (Real.sqrt x * Real.sqrt (x / U)) / 2 := by ring
      _ = _ := by rw [sqrt_scale_endpoint x U hx.le hu]; ring
  have hCend : C / Real.sqrt V = (1 / Real.sqrt 2) * (x / Real.sqrt V) := by dsimp [C]; ring
  rw [hratio, hprod, hBend, hCend] at hbound
  have hL1 : 0 ≤ Real.log (x / (U * V)) := Real.log_nonneg ((le_div_iff₀ (mul_pos hu hv)).mpr (by nlinarith))
  have hM : 0 ≤ Real.log (x / U) := Real.log_nonneg (hV1.trans hVU)
  have hL2 : 0 ≤ Real.log (V * x / U) := by
    apply Real.log_nonneg
    rw [← hprod]
    nlinarith
  have hr := typeII_round_constants (x / Real.sqrt q) (x / Real.sqrt (x / q))
    (x / Real.sqrt U) (x / Real.sqrt V)
    (Real.log (x / (U * V)) * Real.log (V * x / U)) (Real.log (x / U))
    (by positivity) (by positivity) (by positivity) (by positivity) (mul_nonneg hL1 hL2) hM
  simp only [← mul_assoc] at hr
  apply le_trans _ hr
  convert hbound using 1 <;> first | rfl | (dsimp [A]; ring)

end TaoFivePrimes


