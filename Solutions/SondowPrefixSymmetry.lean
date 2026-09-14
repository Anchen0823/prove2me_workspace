import Solutions.SondowRectangleIdentity

open Finset

namespace EulerMascheroni.Sondow

theorem antisymmetric_prefix_reflection (w : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n+1)
    (hw : ∀ i ≤ n, w (n-i) = -w i) :
    (∑ i ∈ range k, w i) = ∑ i ∈ range (n+1-k), w i := by
  have hfull : (∑ i ∈ range (n+1), w i) = 0 := by
    have he : (∑ i ∈ range (n+1), w i) = -(∑ i ∈ range (n+1), w i) := by
      conv_lhs => rw [← sum_range_reflect]
      simp only [Nat.add_sub_cancel]
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro i hi
      exact hw i (by have := mem_range.mp hi; omega)
    linarith
  have htail : (∑ j ∈ range (n+1-k), w (k+j)) = -(∑ i ∈ range (n+1-k), w i) := by
    conv_lhs => rw [← sum_range_reflect]
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i hi
    have hi' : i < n+1-k := mem_range.mp hi
    rw [show k+(n+1-k-1-i) = n-i by omega]
    exact hw i (by omega)
  have hsplit := sum_range_add w k (n+1-k)
  rw [Nat.add_sub_of_le hk, hfull, htail] at hsplit
  linarith

noncomputable def harmonicRowWeight (n i : ℕ) : ℝ :=
  (n.choose i:ℝ)^2*((harmonic (n-i):ℝ)-(harmonic i:ℝ))

theorem harmonicRowWeight_reflection (n i : ℕ) (hi : i ≤ n) :
    harmonicRowWeight n (n-i) = -harmonicRowWeight n i := by
  unfold harmonicRowWeight
  rw [Nat.choose_symm hi, Nat.sub_sub_self hi]
  ring

theorem harmonic_prefix_min (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (∑ i ∈ range k, harmonicRowWeight n i) =
      ∑ i ∈ range (min (k-1) (n-k)+1), harmonicRowWeight n i := by
  by_cases hh : k-1 ≤ n-k
  · rw [min_eq_left hh, Nat.sub_add_cancel hk]
  · rw [min_eq_right (by omega)]
    have he := antisymmetric_prefix_reflection (harmonicRowWeight n) n k (by omega)
      (harmonicRowWeight_reflection n)
    simpa only [show n+1-k = n-k+1 by omega] using he

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.harmonic_prefix_min
