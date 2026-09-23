import examples.«magic-squares».spencer.ClosedIntervalIndicator

set_option autoImplicit false

namespace MagicSquaresEuler

open Finset

/-- Any finite pointwise relation between indicators of nonempty compact real
intervals preserves the sum of their weights, including degenerate intervals. -/
theorem closedInterval_indicator_relation {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (w : ι → ℚ) (hab : ∀ i, a i ≤ b i)
    (h : ∀ x : ℝ, (∑ i, if a i ≤ x ∧ x ≤ b i then w i else 0) = 0) :
    (∑ i, w i) = 0 := by
  classical
  have hgroup (r : ℝ) : (∑ i ∈ Finset.univ.filter (fun i => b i = r), w i) = 0 := by
    obtain ⟨t, hrt, hgap⟩ := exists_right_gap
      ((Finset.univ.image a) ∪ (Finset.univ.image b)) r
    have hdiff (i : ι) :
        (if a i ≤ r ∧ r ≤ b i then w i else 0) -
        (if a i ≤ t ∧ t ≤ b i then w i else 0) =
        if b i = r then w i else 0 := by
      by_cases hbr : b i = r
      · have hai : a i ≤ r := hbr ▸ hab i
        simp [hbr, hai, not_le_of_gt hrt]
      · by_cases hbi : b i < r
        · have hbt : b i < t := hbi.trans hrt
          simp [hbr, not_le_of_gt hbi, not_le_of_gt hbt]
        · have hrb : r < b i := lt_of_le_of_ne (le_of_not_gt hbi) (Ne.symm hbr)
          have htb : t < b i := hgap (b i)
            (mem_union_right _ (mem_image_of_mem b (mem_univ i))) hrb
          by_cases hai : a i ≤ r
          · have hat : a i ≤ t := hai.trans hrt.le
            simp [hbr, hai, hat, hrb.le, htb.le]
          · have hra : r < a i := lt_of_not_ge hai
            have hta : t < a i := hgap (a i)
              (mem_union_left _ (mem_image_of_mem a (mem_univ i))) hra
            simp [hbr, hai, not_le_of_gt hta]
    rw [Finset.sum_filter]
    calc
      _ = ∑ i, ((if a i ≤ r ∧ r ≤ b i then w i else 0) -
          (if a i ≤ t ∧ t ≤ b i then w i else 0)) :=
        Finset.sum_congr rfl (fun i _ => (hdiff i).symm)
      _ = 0 := by rw [Finset.sum_sub_distrib, h r, h t, sub_self]
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset ι)) (t := Finset.univ.image b) (g := b)
    (fun i hi => mem_image_of_mem b hi) w
  rw [← hf]
  exact Finset.sum_eq_zero (fun r _ => hgroup r)

end MagicSquaresEuler
