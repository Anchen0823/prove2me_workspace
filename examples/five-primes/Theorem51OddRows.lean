import examples.«five-primes».Theorem51OddBilinearPhase

namespace TaoFivePrimes
open Finset

lemma odd_rows_reindex {M : Type*} [AddCommMonoid M] (l u : ℤ) (F : ℤ → M) :
    (∑ w ∈ (Icc l u).image (fun n => 2 * n + 1), F w) =
      ∑ j ∈ range (u + 1 - l).toNat, F (2 * (l + (j : ℤ)) + 1) := by
  rw [sum_image (by intro a ha b hb hab; change 2 * a + 1 = 2 * b + 1 at hab; omega),
    Int.Icc_eq_finset_map, sum_map]
  rfl

lemma odd_rows_card (l u : ℤ) :
    ((Icc l u).image (fun n => 2 * n + 1)).card = (u + 1 - l).toNat := by
  rw [card_image_of_injective _ (by intro a b hab; change 2 * a + 1 = 2 * b + 1 at hab; omega), Int.card_Icc]

lemma mem_odd_rows (l u w : ℤ) :
    w ∈ (Icc l u).image (fun n => 2 * n + 1) ↔
      2 * l + 1 ≤ w ∧ w ≤ 2 * u + 1 ∧ w % 2 = 1 := by
  constructor
  · intro hw
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hw
    simp only [mem_Icc] at hn
    omega
  · intro hw
    apply mem_image.mpr
    refine ⟨w / 2, mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩ <;> omega

/-- Literal odd-row interval version, including an empty interval. -/
theorem unit_odd_rectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q alpha : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ 4 * alpha) (hhi : 4 * alpha ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (l u : ℤ) (a : ℤ → ℂ) (x : ι → ℂ) :
    ‖∑ w ∈ (Icc l u).image (fun n => 2 * n + 1), a w *
      (∑ m, expCircle (alpha * ((2 * idx m + 1 : ℤ) : ℝ) * w) * x m)‖ ≤
      Real.sqrt (((((Icc l u).image (fun n => 2 * n + 1)).card : ℝ) + 2 * q - 1) *
        (∑ m, ‖x m‖ ^ 2) * ∑ w ∈ (Icc l u).image (fun n => 2 * n + 1), ‖a w‖ ^ 2) := by
  rw [odd_rows_card, odd_rows_reindex, odd_rows_reindex]
  have hb := unit_odd_bilinear_block idx hinj q alpha hq hlo hhi hwidth
    (u + 1 - l).toNat ((l : ℝ) + 1 / 2) (fun j => a (2 * (l + (j : ℤ)) + 1)) x
  have he (j : ℕ) : ((2 * (l + (j : ℤ)) + 1 : ℤ) : ℝ) =
      2 * ((j : ℝ) + ((l : ℝ) + 1 / 2)) := by push_cast; ring
  simpa only [he] using hb

end TaoFivePrimes
