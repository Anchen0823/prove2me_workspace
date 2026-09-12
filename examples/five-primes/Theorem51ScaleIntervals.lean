import Definitions.Def_TaoFivePrimes_Theorem51Scale
import examples.«five-primes».Theorem51ColumnPartition
import examples.«five-primes».Theorem51TypeIICounts
import examples.«five-primes».Theorem51OddRows

namespace TaoFivePrimes
open Finset

lemma mem_oddHalfInterval (A B : ℝ) (n : ℤ) :
    n ∈ oddHalfInterval A B ↔ A ≤ ((2 * n + 1 : ℤ) : ℝ) ∧
      ((2 * n + 1 : ℤ) : ℝ) ≤ B := by
  simp only [oddHalfInterval, mem_Icc, Int.ceil_le, Int.le_floor,
    Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
  constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith

lemma mem_oddRealInterval (A B : ℝ) (w : ℤ) :
    w ∈ oddRealInterval A B ↔ A ≤ (w : ℝ) ∧ (w : ℝ) ≤ B ∧ w % 2 = 1 := by
  constructor
  · intro hw
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hw
    have hh := (mem_oddHalfInterval A B n).mp hn
    exact ⟨hh.1, hh.2, by omega⟩
  · intro hw
    have he : 2 * (w / 2) + 1 = w := by omega
    apply mem_image.mpr
    refine ⟨w / 2, (mem_oddHalfInterval A B _).mpr ?_, he⟩
    rw [he]
    exact ⟨hw.1, hw.2.1⟩

lemma odd_interval_card_eq (A B : ℝ) :
    (oddRealInterval A B).card = (oddHalfInterval A B).card := by
  apply card_image_of_injective
  intro m n he
  change 2 * m + 1 = 2 * n + 1 at he
  omega

lemma odd_half_span (A B : ℝ) :
    (⌊(B - 1) / 2⌋ : ℝ) - (⌈(A - 1) / 2⌉ : ℝ) ≤ (B - A) / 2 := by
  have hB := Int.floor_le ((B - 1) / 2)
  have hA := Int.le_ceil ((A - 1) / 2)
  linarith

lemma odd_real_interval_count (A B : ℝ) (hAB : A ≤ B) :
    ((oddRealInterval A B).card : ℝ) ≤ (B - A) / 2 + 1 :=
  odd_integer_interval_card _ A B hAB (fun w hw => (mem_oddRealInterval A B w).mp hw)

lemma scale_row_counts (W : ℝ) (hW : 40 ≤ W) :
    ((oddRealInterval (W / 2) W).card : ℝ) - 1 ≤ W / 4 ∧
      ((oddRealInterval (W / 2) W).card : ℝ) ≤ 1.1 * W / 4 := by
  have hc := odd_real_interval_count (W / 2) W (by linarith)
  constructor <;> linarith

lemma scale_column_count (x W : ℝ) (hW : 0 < W) (hxW : 40 ≤ x / W) :
    ((oddHalfInterval (x / (2 * W)) (x / W)).card : ℝ) ≤ 1.1 * x / (4 * W) := by
  rw [← odd_interval_card_eq]
  exact odd_column_count _ x W hW hxW (fun d hd =>
    (mem_oddRealInterval (x / (2 * W)) (x / W) d).mp hd)

lemma scale_column_block_count (x W : ℝ) (q : ℕ) (hW : 0 < W) (hx : 0 ≤ x)
    (hq : 0 < q) :
    ((((⌊(x / W - 1) / 2⌋ - ⌈(x / (2 * W) - 1) / 2⌉ : ℤ).toNat /
      ((q + 1) / 2)) + 1 : ℕ) : ℝ) ≤ x / (2 * W * q) + 1 := by
  have hspan := odd_half_span (x / (2 * W)) (x / W)
  have he : (x / W - x / (2 * W)) / 2 = x / (4 * W) := by ring
  rw [he] at hspan
  have hb := integer_block_count ⌈(x / (2 * W) - 1) / 2⌉ ⌊(x / W - 1) / 2⌋
    ((q + 1) / 2) q (x / (4 * W)) (by exact_mod_cast hq)
    (by positivity) (half_modulus_block_size q).1 hspan
  have he' : 2 * (x / (4 * W)) / (q : ℝ) + 1 = x / (2 * W * q) + 1 := by ring
  rwa [he'] at hb

end TaoFivePrimes


