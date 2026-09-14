import Mathlib.Tactic

open Finset

namespace EulerMascheroni.Sondow

/-- Pair the strict lower and upper triangles of a symmetric finite matrix. -/
theorem symmetric_square_sum (f : ℕ → ℕ → ℝ) (hsymm : ∀ i j, f i j = f j i) (m : ℕ) :
    (∑ i ∈ range m, ∑ j ∈ range m, f i j) =
      (∑ i ∈ range m, f i i) + 2 * ∑ j ∈ range m, ∑ i ∈ range j, f i j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : (∑ i ∈ range (m+1), ∑ j ∈ range (m+1), f i j) =
        (∑ i ∈ range m, ∑ j ∈ range m, f i j) +
          (∑ i ∈ range m, f i m) + (∑ j ∈ range m, f m j) + f m m := by
      rw [sum_range_succ]
      simp_rw [sum_range_succ]
      rw [sum_add_distrib]
      ring
    have he : (∑ j ∈ range m, f m j) = ∑ i ∈ range m, f i m := by
      apply sum_congr rfl
      intro i hi
      exact hsymm m i
    rw [hsplit, ih, he, sum_range_succ, sum_range_succ]
    ring

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.symmetric_square_sum
