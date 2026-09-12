import examples.«five-primes».Theorem51ColumnPartition
import examples.«five-primes».Theorem51OddRows

namespace TaoFivePrimes
open Finset

/-- The concrete column partition feeds the bilinear estimate and preserves
the original coefficient energy. -/
theorem unit_padded_odd_rectangle (q alpha : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ 4 * alpha) (hhi : 4 * alpha ≤ (q + 1) / q ^ 2)
    (L R l u : ℤ) (K M : ℕ) (hcover : (R + 1 - L).toNat ≤ K * M)
    (hsize : (M : ℝ) - 1 ≤ q / 2) (a c : ℤ → ℂ) :
    ‖∑ w ∈ (Icc l u).image (fun n => 2 * n + 1), a w *
      (∑ n ∈ Icc L R, expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * c n)‖ ≤
      Real.sqrt ((K : ℝ) *
        (((((Icc l u).image (fun n => 2 * n + 1)).card : ℝ) + 2 * q - 1) *
          (∑ n ∈ Icc L R, ‖c n‖ ^ 2)) *
        ∑ w ∈ (Icc l u).image (fun n => 2 * n + 1), ‖a w‖ ^ 2) := by
  let idx (b : ℕ) (m : Fin M) : ℤ := L + ((b * M + m.val : ℕ) : ℤ)
  let cp (b : ℕ) (m : Fin M) : ℂ := if idx b m ≤ R then c (idx b m) else 0
  let rows := (Icc l u).image (fun n => 2 * n + 1)
  let F (b : ℕ) : ℂ := ∑ w ∈ rows, a w *
    (∑ m : Fin M, expCircle (alpha * ((2 * idx b m + 1 : ℤ) : ℝ) * w) * cp b m)
  have hinj (b : ℕ) : Function.Injective (idx b) := by
    intro m n he
    apply Fin.ext
    dsimp [idx] at he
    omega
  have hwidth (b : ℕ) (m n : Fin M) : |(idx b m : ℝ) - (idx b n : ℝ)| ≤ q / 2 := by
    have hm : (m.val : ℝ) + 1 ≤ M := by exact_mod_cast m.isLt
    have hn : (n.val : ℝ) + 1 ≤ M := by exact_mod_cast n.isLt
    have hm0 : (0 : ℝ) ≤ m.val := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ n.val := Nat.cast_nonneg _
    dsimp [idx]
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have henergy : (∑ b ∈ range K, ∑ m : Fin M, ‖cp b m‖ ^ 2) = ∑ n ∈ Icc L R, ‖c n‖ ^ 2 := by
    have he := integer_interval_blocks_energy L R K M hcover c
    conv_lhs at he => arg 2; ext b; rw [← Fin.sum_univ_eq_sum_range]
    exact he
  have hinner (w : ℤ) :
      (∑ n ∈ Icc L R, expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * c n) =
      ∑ b ∈ range K, ∑ m : Fin M,
        expCircle (alpha * ((2 * idx b m + 1 : ℤ) : ℝ) * w) * cp b m := by
    have he := integer_interval_blocks L R K M hcover
      (fun n => expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * c n)
    conv_lhs at he => arg 2; ext b; rw [← Fin.sum_univ_eq_sum_range]
    simpa only [cp, idx, mul_ite, mul_zero] using he.symm
  have hsum : (∑ w ∈ rows, a w *
      (∑ n ∈ Icc L R, expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * c n)) =
      ∑ b ∈ range K, F b := by
    simp only [hinner, mul_sum, F]
    rw [sum_comm]
  let C : ℝ := (rows.card : ℝ) + 2 * q - 1
  let E : ℝ := ∑ w ∈ rows, ‖a w‖ ^ 2
  have hb (b : ℕ) : ‖F b‖ ^ 2 ≤ C * (∑ m : Fin M, ‖cp b m‖ ^ 2) * E := by
    have hh := unit_odd_rectangle (idx b) (hinj b) q alpha hq hlo hhi (hwidth b) l u a (cp b)
    have hC : 0 ≤ C := by dsimp [C]; have hc := Nat.cast_nonneg rows.card (α := ℝ); linarith
    have hE : 0 ≤ E := sum_nonneg fun w hw => sq_nonneg _
    exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg
      (mul_nonneg hC (sum_nonneg fun m hm => sq_nonneg _)) hE)).mp hh
  change ‖∑ w ∈ rows, a w * _‖ ≤ _
  rw [hsum]
  apply Real.le_sqrt_of_sq_le
  apply (complex_sum_sq_le_card_energy (range K) F).trans
  have hh := sum_le_sum (s := range K) (fun b hb' => hb b)
  have hmul := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  rw [← sum_mul, ← mul_sum, henergy] at hmul
  simpa only [card_range, C, E, rows, mul_assoc] using hmul

end TaoFivePrimes
