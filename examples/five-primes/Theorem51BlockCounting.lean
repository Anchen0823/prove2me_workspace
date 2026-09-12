import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace TaoFivePrimes
open Finset

/-- An integer set of diameter at most L contains at most L+1 points. -/
theorem integer_set_card_le (s : Finset ℤ) (L : ℝ) (hL : 0 ≤ L)
    (hdiam : ∀ a ∈ s, ∀ b ∈ s, |(a : ℝ) - (b : ℝ)| ≤ L) :
    (s.card : ℝ) - 1 ≤ L := by
  by_cases hs : s.Nonempty
  · have hmin := s.min'_mem hs
    have hmax := s.max'_mem hs
    have horder : s.min' hs ≤ s.max' hs := s.min'_le _ hmax
    have hsub : s ⊆ Icc (s.min' hs) (s.max' hs) := by
      intro a ha
      exact mem_Icc.mpr ⟨s.min'_le a ha, s.le_max' a ha⟩
    have hc := card_le_card hsub
    have hi := Int.card_Icc_of_le (s.min' hs) (s.max' hs) (show s.min' hs ≤ s.max' hs + 1 by omega)
    have hiR : ((Icc (s.min' hs) (s.max' hs)).card : ℝ) =
        (s.max' hs : ℝ) + 1 - (s.min' hs : ℝ) := by exact_mod_cast hi
    have hcR : (s.card : ℝ) ≤ ((Icc (s.min' hs) (s.max' hs)).card : ℝ) := by exact_mod_cast hc
    have hd := hdiam _ hmax _ hmin
    rw [hiR] at hcR
    linarith [le_abs_self ((s.max' hs : ℝ) - (s.min' hs : ℝ))]
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp only [he, card_empty, Nat.cast_zero, zero_sub]
    linarith

theorem integer_index_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (L : ℝ) (hL : 0 ≤ L)
    (hdiam : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ L) :
    (Fintype.card ι : ℝ) - 1 ≤ L := by
  have hc := integer_set_card_le (univ.image idx) L hL (by
    intro a ha b hb
    obtain ⟨m, hm, rfl⟩ := mem_image.mp ha
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hb
    exact hdiam m n)
  simpa only [card_image_of_injective _ hinj, card_univ] using hc

/-- Odd integers in a real interval have density at most one half, with
one endpoint allowance. This retains the constants in Type II counting. -/
theorem odd_integer_interval_card (s : Finset ℤ) (A B : ℝ) (hAB : A ≤ B)
    (hs : ∀ n ∈ s, A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B ∧ n % 2 = 1) :
    (s.card : ℝ) ≤ (B - A) / 2 + 1 := by
  have hid (n : ℤ) (hn : n ∈ s) : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) + 1 := by
    have hm := (hs n hn).2.2
    have he : n = 2 * (n / 2) + 1 := by omega
    exact_mod_cast he
  have hi : Set.InjOn (fun n : ℤ => n / 2) (s : Set ℤ) := by
    intro m hm n hn he
    change m / 2 = n / 2 at he
    have hm' := (hs m hm).2.2
    have hn' := (hs n hn).2.2
    omega
  have hc := integer_set_card_le (s.image (fun n => n / 2)) ((B - A) / 2)
    (by linarith) (by
      intro a ha b hb
      obtain ⟨m, hm, rfl⟩ := mem_image.mp ha
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hb
      have hm' := hs m hm
      have hn' := hs n hn
      have em := hid m hm
      have en := hid n hn
      rw [abs_le]
      constructor <;> linarith)
  rw [Finset.card_image_iff.mpr hi] at hc
  linarith

end TaoFivePrimes
