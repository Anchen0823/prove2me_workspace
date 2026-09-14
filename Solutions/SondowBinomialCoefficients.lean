import Solutions.SondowSymmetricSums
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Sum

open Finset

namespace EulerMascheroni.Sondow

theorem signed_choose_sum (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ range (n+1), (-1:ℝ)^i*(n.choose i:ℝ)) = 0 := by
  exact_mod_cast Int.alternating_sum_range_choose_of_ne hn.ne'

theorem choose_square_sum (n : ℕ) :
    (∑ i ∈ range (n+1), (n.choose i:ℝ)^2) = ((2*n).choose n:ℝ) := by
  exact_mod_cast Nat.sum_range_choose_sq n

/-- Coefficient of log N after pairing the off-diagonal moments. -/
theorem signed_triangular_choose_sum (n : ℕ) (hn : 0 < n) :
    2 * (∑ j ∈ range (n+1), ∑ i ∈ range j,
      (-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) = -((2*n).choose n:ℝ) := by
  let c (i : ℕ) : ℝ := (-1:ℝ)^i*(n.choose i:ℝ)
  have hs : (∑ i ∈ range (n+1), ∑ j ∈ range (n+1), c i*c j) = 0 := by
    simp_rw [← mul_sum]
    change (∑ i ∈ range (n+1), c i *
      (∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ))) = 0
    rw [signed_choose_sum n hn]
    simp
  have hd : (∑ i ∈ range (n+1), c i*c i) = ((2*n).choose n:ℝ) := by
    rw [← choose_square_sum]
    apply sum_congr rfl
    intro i hi
    have he : (-1:ℝ)^i * (-1:ℝ)^i = 1 := by
      rw [← pow_add, ← two_mul i, pow_mul]
      norm_num
    dsimp only [c]
    nlinarith [he]
  have he := symmetric_square_sum (fun i j => c i*c j) (fun i j => mul_comm _ _) (n+1)
  rw [hs, hd] at he
  have ht : (∑ j ∈ range (n+1), ∑ i ∈ range j, c i*c j) =
      ∑ j ∈ range (n+1), ∑ i ∈ range j,
        (-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ) := by
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro i hi
    dsimp only [c]
    rw [pow_add]
    ring
  rw [ht] at he
  linarith

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.signed_triangular_choose_sum
