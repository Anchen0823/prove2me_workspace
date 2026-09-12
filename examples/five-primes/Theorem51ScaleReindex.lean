import examples.«five-primes».Theorem51NatOddReindex

namespace TaoFivePrimes
open Finset

lemma nat_odd_column_sum (A B alpha U w : ℝ) (N : ℕ) (hA : 0 < A) (hB : B ≤ N) :
    (∑ d ∈ Icc 1 N, if A ≤ (d : ℝ) ∧ (d : ℝ) ≤ B ∧ d.Coprime 2 then
      expCircle (alpha * d * w) *
        (if U < (d : ℝ) then (ArithmeticFunction.moebius d : ℂ) else 0) else 0) =
      ∑ n ∈ oddHalfInterval A B,
        expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * scaleColumnCoefficient U n := by
  rw [nat_odd_interval_sum A B N hA hB]
  unfold oddRealInterval
  rw [sum_image (by intro m hm n hn he; change 2 * m + 1 = 2 * n + 1 at he; omega)]
  apply sum_congr rfl
  intro n hn
  have hp : 0 ≤ (2 * n + 1 : ℤ) := by
    have hh := (mem_oddHalfInterval A B n).mp hn
    exact_mod_cast (hA.trans_le hh.1).le
  have he : ((2 * n + 1).toNat : ℝ) = ((2 * n + 1 : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hp)
  simp only [he, scaleColumnCoefficient]

noncomputable def theorem51NatScaleSum (x alpha U V W : ℝ) : ℂ :=
  ∑ w ∈ Icc 1 ⌈x⌉₊, if W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W ∧ w.Coprime 2 then
    (if V < (w : ℝ) then (theorem51Centered V w : ℂ) else 0) *
      (∑ d ∈ Icc 1 ⌈x⌉₊, if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ d.Coprime 2 then
        expCircle (alpha * d * w) *
          (if U < (d : ℝ) then (ArithmeticFunction.moebius d : ℂ) else 0) else 0)
    else 0

lemma theorem51NatScaleSum_eq (x alpha U V W : ℝ)
    (hx : 0 < x) (hW : 1 ≤ W) (hWx : W ≤ x) :
    theorem51NatScaleSum x alpha U V W = theorem51ScaleSum x alpha U V W := by
  have hw : 0 < W := by linarith
  have hcol : x / W ≤ (⌈x⌉₊ : ℝ) := by
    apply le_trans _ (Nat.le_ceil x)
    apply (div_le_iff₀ hw).mpr
    nlinarith
  unfold theorem51NatScaleSum
  rw [nat_odd_interval_sum (W / 2) W ⌈x⌉₊ (by positivity) (hWx.trans (Nat.le_ceil x))]
  unfold theorem51ScaleSum
  apply sum_congr rfl
  intro w hwmem
  have hp : 0 ≤ w := by
    have hh := (mem_oddRealInterval (W / 2) W w).mp hwmem
    exact_mod_cast (show (0 : ℝ) ≤ w by linarith [hh.1])
  have he : (w.toNat : ℝ) = (w : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg hp)
  rw [nat_odd_column_sum (x / (2 * W)) (x / W) alpha U w.toNat ⌈x⌉₊ (by positivity) hcol]
  simp only [he, scaleRowCoefficient]

end TaoFivePrimes
