import examples.«five-primes».Theorem51CutoffAmplitude
import examples.«five-primes».Theorem51DiscreteSecondDifference
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

namespace TaoFivePrimes

lemma expCircle_odd_geometric (alpha d : ℝ) (n : ℤ) :
    expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ)) =
      expCircle (alpha * d) *
        (Complex.exp (Complex.I * ((4 * Real.pi * d * alpha : ℝ) : ℂ))) ^ n := by
  unfold expCircle
  rw [← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma expCircle_norm_unit (t : ℝ) : ‖expCircle t‖ = 1 := by
  unfold expCircle
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
    Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) by push_cast; ring]
  exact Complex.norm_exp_I_mul_ofReal _

/-- Removing the harmless unit phase is exact, for every integer-indexed amplitude. -/
lemma norm_odd_fourier_eq_geometric (alpha d : ℝ) (F : ℤ → ℂ) :
    ‖∑' n : ℤ, F n * expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ))‖ =
      ‖∑' n : ℤ, F n *
        (Complex.exp (Complex.I * ((4 * Real.pi * d * alpha : ℝ) : ℂ))) ^ n‖ := by
  simp_rw [expCircle_odd_geometric, mul_left_comm (F _) (expCircle (alpha * d))]
  rw [tsum_mul_left, norm_mul, expCircle_norm_unit, one_mul]

/-- Actual odd-lattice Type I sum: no smoothness hypothesis is used. -/
theorem typeI_odd_sum_second_difference_bound (x d alpha : ℝ) (c : ℂ)
    (hx : 0 < x) (hd : 0 < d) (hsin : Real.sin (2 * Real.pi * d * alpha) ≠ 0) :
    ‖∑' n : ℤ, typeIOddAmplitude x d c n *
      expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ))‖ ≤
    (∑' n : ℤ, ‖typeIOddAmplitude x d c (n + 2) -
      2 * typeIOddAmplitude x d c (n + 1) + typeIOddAmplitude x d c n‖) /
      (4 * Real.sin (2 * Real.pi * d * alpha) ^ 2) := by
  rw [norm_odd_fourier_eq_geometric]
  let theta : ℝ := 4 * Real.pi * d * alpha
  let z : ℂ := Complex.exp (Complex.I * (theta : ℂ))
  have hz : ‖z‖ = 1 := Complex.norm_exp_I_mul_ofReal theta
  have hgap : ‖1 - z‖ ^ 2 = 4 * Real.sin (2 * Real.pi * d * alpha) ^ 2 := by
    dsimp [z]
    rw [norm_exp_gap_sq, show theta / 2 = 2 * Real.pi * d * alpha by dsimp [theta]; ring]
  have hz1 : z ≠ 1 := by
    intro he
    rw [he, sub_self, norm_zero, zero_pow (by decide)] at hgap
    nlinarith [sq_pos_of_ne_zero hsin]
  have h := finite_fourier_second_difference_bound z hz hz1
    (typeIOddAmplitude x d c) (typeIOddAmplitude_finite x d c hx hd)
  rw [hgap] at h
  exact h

end TaoFivePrimes
