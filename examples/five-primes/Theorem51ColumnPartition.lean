import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace TaoFivePrimes
open Finset

/-- Consecutive full blocks enumerate a finite range exactly once. -/
theorem range_blocks_sum {A : Type*} [AddCommMonoid A]
    (K M : ℕ) (F : ℕ → A) :
    (∑ b ∈ range K, ∑ m ∈ range M, F (b * M + m)) = ∑ n ∈ range (K * M), F n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih, Nat.succ_mul, sum_range_add]

/-- Padding only beyond the end of the original range preserves its sum. -/
theorem range_blocks_zero_pad {A : Type*} [AddCommMonoid A]
    (D K M : ℕ) (hcover : D ≤ K * M) (F : ℕ → A) :
    (∑ b ∈ range K, ∑ m ∈ range M, if b * M + m < D then F (b * M + m) else 0) =
      ∑ n ∈ range D, F n := by
  rw [range_blocks_sum K M (fun n => if n < D then F n else 0)]
  symm
  calc
    _ = ∑ n ∈ range D, if n < D then F n else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [if_pos (mem_range.mp hn)]
    _ = ∑ n ∈ range (K * M), if n < D then F n else 0 := by
      apply sum_subset (range_mono hcover)
      intro n hn hnD
      exact if_neg (by simpa only [mem_range] using hnD)

/-- Integer interval subdivision, valid also when the interval is empty. -/
theorem integer_interval_blocks {A : Type*} [AddCommMonoid A]
    (l u : ℤ) (K M : ℕ) (hcover : (u + 1 - l).toNat ≤ K * M) (F : ℤ → A) :
    (∑ b ∈ range K, ∑ m ∈ range M,
      if l + ((b * M + m : ℕ) : ℤ) ≤ u then F (l + ((b * M + m : ℕ) : ℤ)) else 0) =
      ∑ n ∈ Icc l u, F n := by
  rw [Int.Icc_eq_finset_map, sum_map]
  change _ = ∑ n ∈ range (u + 1 - l).toNat, F (l + (n : ℤ))
  have hb := range_blocks_zero_pad (u + 1 - l).toNat K M hcover (fun n => F (l + (n : ℤ)))
  convert hb using 1
  apply sum_congr rfl
  intro b hb
  apply sum_congr rfl
  intro m hm
  have he : l + ((b * M + m : ℕ) : ℤ) ≤ u ↔ b * M + m < (u + 1 - l).toNat := by omega
  simp only [he]

theorem integer_interval_blocks_energy (l u : ℤ) (K M : ℕ)
    (hcover : (u + 1 - l).toNat ≤ K * M) (c : ℤ → ℂ) :
    (∑ b ∈ range K, ∑ m ∈ range M,
      ‖if l + ((b * M + m : ℕ) : ℤ) ≤ u then c (l + ((b * M + m : ℕ) : ℤ)) else 0‖ ^ 2) =
      ∑ n ∈ Icc l u, ‖c n‖ ^ 2 := by
  have hb := integer_interval_blocks l u K M hcover (fun n => ‖c n‖ ^ 2)
  simpa only [apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero, zero_pow (by decide : 2 ≠ 0)] using hb

/-- This many full blocks cover the interval; the same formula handles an
empty interval through zero padding. -/
theorem integer_block_cover (l u : ℤ) (M : ℕ) (hM : 0 < M) :
    (u + 1 - l).toNat ≤ ((u - l).toNat / M + 1) * M := by
  have hd := Nat.mod_lt (u - l).toNat hM
  have he := Nat.mod_add_div (u - l).toNat M
  rw [Nat.mul_comm M] at he
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem integer_block_count (l u : ℤ) (M : ℕ) (q L : ℝ) (hq : 0 < q)
    (hL : 0 ≤ L) (hsize : q / 2 ≤ (M : ℝ)) (hspan : (u : ℝ) - (l : ℝ) ≤ L) :
    (((u - l).toNat / M + 1 : ℕ) : ℝ) ≤ 2 * L / q + 1 := by
  have hspan' : ((u - l).toNat : ℝ) ≤ L := by
    by_cases hh : 0 ≤ u - l
    · have he : ((u - l).toNat : ℝ) = (u : ℝ) - (l : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg hh)
      rwa [he]
    · rw [Int.toNat_eq_zero.mpr (by omega), Nat.cast_zero]
      exact hL
  have hd : (((u - l).toNat / M : ℕ) : ℝ) * M ≤ ((u - l).toNat : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (u - l).toNat M
  have hm := mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg ((u - l).toNat / M) :
    (0 : ℝ) ≤ ((u - l).toNat / M : ℕ))
  have hb : (((u - l).toNat / M : ℕ) : ℝ) ≤ 2 * L / q := by
    apply (le_div_iff₀ hq).mpr
    nlinarith
  push_cast
  linarith

theorem half_modulus_block_size (q : ℕ) :
    (q : ℝ) / 2 ≤ (((q + 1) / 2 : ℕ) : ℝ) ∧
      (((q + 1) / 2 : ℕ) : ℝ) - 1 ≤ (q : ℝ) / 2 := by
  have hlo : q ≤ 2 * ((q + 1) / 2) := by omega
  have hhi : 2 * ((q + 1) / 2) ≤ q + 1 := by omega
  have hloR : (q : ℝ) ≤ 2 * (((q + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hlo
  have hhiR : 2 * (((q + 1) / 2 : ℕ) : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hhi
  constructor <;> linarith

end TaoFivePrimes
