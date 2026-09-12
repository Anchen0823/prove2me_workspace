import examples.«five-primes».Theorem51AmplitudePrimitive
import examples.«five-primes».Theorem51VariationTransfer
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace TaoFivePrimes

open MeasureTheory

theorem typeI_finite_second_difference_bound (r d a : ℝ) (c : ℂ) (N : ℕ)
    (hr : 4 ≤ r) (hd : 1 ≤ d) (hc : ‖c‖ ≤ 1) :
    (∑ n ∈ Finset.range N,
      ‖typeIRealAmplitude r d c (a + 2 * (n + 2)) -
        2 * typeIRealAmplitude r d c (a + 2 * (n + 1)) + typeIRealAmplitude r d c (a + 2 * n)‖) ≤
      96 * Real.log (4 * (d * r)) / r := by
  have hr0 : 0 < r := by linarith
  have hlog : 0 ≤ Real.log (4 * (d * r)) := Real.log_nonneg (by nlinarith)
  have h := second_difference_from_bounded_variation (typeIRealAmplitude r d c)
    (typeIPiecewiseSlope r d c) a (48 * Real.log (4 * (d * r)) / r) N (by positivity)
    (by
      intro n
      have hi := (typeI_slope_intervalIntegrable r d c hr0 (a + 2 * n) (a + 2 * n + 2)).comp_add_left (a + 2 * n)
      simpa only [sub_self, add_sub_cancel_left] using hi)
    (by
      intro n
      rw [intervalIntegral.integral_comp_add_left]
      simp only [add_zero]
      rw [typeI_slope_integral r d c hr0 _ _ (by linarith)]
      congr 1
      congr 1
      ring)
    (typeI_piecewise_slope_variation r d c hr hd hc)
  convert h using 1
  ring

/-- Passing from finite prefixes to the whole odd integer lattice. The shift
by one includes the possible first nonzero second difference at index -1. -/
theorem odd_integer_second_difference_of_prefix_bound (F : ℝ → ℂ) (B : ℝ)
    (hzero : ∀ y ≤ 1, F y = 0)
    (hprefix : ∀ N : ℕ, (∑ n ∈ Finset.range N,
      ‖F (-1 + 2 * (n + 2)) - 2 * F (-1 + 2 * (n + 1)) + F (-1 + 2 * n)‖) ≤ B) :
    (∑' n : ℤ, ‖F (2 * (n + 2) + 1) - 2 * F (2 * (n + 1) + 1) + F (2 * n + 1)‖) ≤ B := by
  let D (n : ℤ) := ‖F (2 * (n + 2) + 1) - 2 * F (2 * (n + 1) + 1) + F (2 * n + 1)‖
  let G (n : ℤ) := D (n - 1)
  have he (n : ℕ) : G n =
      ‖F (-1 + 2 * (n + 2)) - 2 * F (-1 + 2 * (n + 1)) + F (-1 + 2 * n)‖ := by
    dsimp [G, D]
    push_cast
    congr 1 <;> congr 1 <;> congr 1 <;> ring
  have hp : ∀ N : ℕ, ∑ n ∈ Finset.range N, G n ≤ B := by
    intro N
    simpa only [he] using hprefix N
  have hn (n : ℕ) : G (-(n + 1)) = 0 := by
    have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    dsimp [G, D]
    push_cast
    rw [hzero _ (by linarith), hzero _ (by linarith), hzero _ (by linarith)]
    simp
  have hs : Summable (fun n : ℕ => G n) := summable_of_sum_range_le (fun n => norm_nonneg _) hp
  have hsneg : Summable (fun n : ℕ => G (-(n + 1))) := by simp only [hn]; exact summable_zero
  have hsum := tsum_of_nat_of_neg_add_one hs hsneg
  simp only [hn, tsum_zero, add_zero] at hsum
  have hshift : (∑' n : ℤ, G n) = ∑' n : ℤ, D n := by
    exact (Equiv.addRight (-1 : ℤ)).tsum_eq D
  change (∑' n : ℤ, D n) ≤ B
  rw [← hshift, hsum]
  exact Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) hp

theorem typeI_integer_second_difference_bound (r d : ℝ) (c : ℂ)
    (hr : 4 ≤ r) (hd : 1 ≤ d) (hc : ‖c‖ ≤ 1) :
    (∑' n : ℤ, ‖typeIRealAmplitude r d c (2 * (n + 2) + 1) -
      2 * typeIRealAmplitude r d c (2 * (n + 1) + 1) + typeIRealAmplitude r d c (2 * n + 1)‖) ≤
      96 * Real.log (4 * (d * r)) / r := by
  apply odd_integer_second_difference_of_prefix_bound
  · intro y hy
    have hr0 : 0 < r := by linarith
    have hcut := eta0_zero_below_quarter ((div_le_iff₀ hr0).mpr (by linarith : y ≤ 1 / 4 * r))
    simp [typeIRealAmplitude, hcut]
  · intro N
    exact typeI_finite_second_difference_bound r d (-1) c N hr hd hc

/-- The formerly assumed concrete Type I variation estimate, now proved. -/
theorem typeI_actual_discrete_variation (x d : ℝ) (c : ℂ)
    (hd : 1 ≤ d) (hdx : 4 * d ≤ x) (hc : ‖c‖ ≤ 1) :
    (∑' n : ℤ, ‖typeIOddAmplitude x d c (n + 2) -
      2 * typeIOddAmplitude x d c (n + 1) + typeIOddAmplitude x d c n‖) ≤
      96 * Real.log (4 * x) / x * d := by
  have hd0 : 0 < d := by linarith
  have hx0 : 0 < x := by linarith
  have hr : 4 ≤ x / d := (le_div_iff₀ hd0).mpr hdx
  have h := typeI_integer_second_difference_bound (x / d) d c hr hd hc
  have he (n : ℤ) : typeIOddAmplitude x d c n = typeIRealAmplitude (x / d) d c (2 * n + 1) := by
    unfold typeIOddAmplitude typeIRealAmplitude
    push_cast
    congr 2
    field_simp
  simp_rw [he]
  have hl : d * (x / d) = x := by field_simp
  rw [hl] at h
  convert h using 1 <;> first | rfl | (push_cast; field_simp)

end TaoFivePrimes
