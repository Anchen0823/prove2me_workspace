import Solutions.SondowBinomialRows

open Finset

namespace EulerMascheroni.Sondow

theorem skew_square_sum_zero (f : ℕ → ℕ → ℝ) (hf : ∀ i j, f i j = -f j i) (k : ℕ) :
    (∑ i ∈ range k, ∑ j ∈ range k, f i j) = 0 := by
  have he : (∑ i ∈ range k, ∑ j ∈ range k, f i j) =
      -(∑ i ∈ range k, ∑ j ∈ range k, f i j) := by
    calc
      _ = ∑ j ∈ range k, ∑ i ∈ range k, f i j := sum_comm
      _ = ∑ j ∈ range k, ∑ i ∈ range k, -f j i := by
        apply sum_congr rfl
        intro j hj
        apply sum_congr rfl
        intro i hi
        exact hf i j
      _ = _ := by simp only [sum_neg_distrib]
  linarith

noncomputable def binomialInteraction (n i j : ℕ) : ℝ :=
  -((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/((j:ℝ)-i)

theorem binomialInteraction_skew (n i j : ℕ) :
    binomialInteraction n i j = -binomialInteraction n j i := by
  unfold binomialInteraction
  rw [Nat.add_comm j i, show (i:ℝ)-j = -((j:ℝ)-i) by ring]
  rw [div_neg]
  ring

theorem binomialInteraction_row (n i : ℕ) (hi : i ≤ n) :
    (∑ j ∈ range (n+1), binomialInteraction n i j) =
      (n.choose i:ℝ)^2*((harmonic (n-i):ℝ)-(harmonic i:ℝ)) := by
  have he : (∑ j ∈ range (n+1), binomialInteraction n i j) =
      -((-1:ℝ)^i*(n.choose i:ℝ))*binomialRow n i := by
    rw [binomialRow, mul_sum]
    apply sum_congr rfl
    intro j hj
    unfold binomialInteraction
    rw [pow_add]
    ring
  rw [he, binomialRow_eq_harmonic n i hi]
  have hsq : (-1:ℝ)^i*(-1:ℝ)^i = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  linear_combination -(n.choose i:ℝ)^2*((harmonic i:ℝ)-(harmonic (n-i):ℝ))*hsq

/-- Sondow's Appendix rectangle identity, expressed without a negative natural exponent. -/
theorem binomial_rectangle_identity (n k : ℕ) (hk : k ≤ n+1) :
    (∑ i ∈ range k, ∑ j ∈ Ico k (n+1),
      -((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ)) =
      ∑ i ∈ range k, (n.choose i:ℝ)^2*
        ((harmonic (n-i):ℝ)-(harmonic i:ℝ)) := by
  have he : (∑ i ∈ range k, ∑ j ∈ Ico k (n+1),
      -((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ))/(j-i:ℕ)) =
      ∑ i ∈ range k, ∑ j ∈ Ico k (n+1), binomialInteraction n i j := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    have hij : i ≤ j := by
      have := mem_range.mp hi
      have := (mem_Ico.mp hj).1
      omega
    simp only [binomialInteraction, Nat.cast_sub hij]
  rw [he]
  simp_rw [sum_Ico_eq_sub _ hk, sum_sub_distrib]
  rw [skew_square_sum_zero _ (binomialInteraction_skew n) k, sub_zero]
  apply sum_congr rfl
  intro i hi
  exact binomialInteraction_row n i (by have := mem_range.mp hi; omega)

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.binomial_rectangle_identity
