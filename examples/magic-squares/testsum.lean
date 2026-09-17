import Mathlib

private def fromComp1 (t : ℕ) (q : Fin 5 → Fin (t + 1)) : Fin 6 → Fin (t + 1) :=
  fun j =>
    if h : (j : ℕ) = 3 then ⟨0, by omega⟩
    else
      if h' : (j : ℕ) < 3 then q ⟨j, by omega⟩
      else q ⟨(j : ℕ) - 1, by omega⟩

private lemma sum_fromComp1 (t : ℕ) (q : Fin 5 → Fin (t + 1)) :
    (∑ i : Fin 6, (fromComp1 t q i : ℕ)) =
      (q 0 : ℕ) + (q 1 : ℕ) + (q 2 : ℕ) + (q 3 : ℕ) + (q 4 : ℕ) := by
  have h0 : (fromComp1 t q 0 : ℕ) = (q 0 : ℕ) := by simp [fromComp1]
  have h1 : (fromComp1 t q 1 : ℕ) = (q 1 : ℕ) := by simp [fromComp1]
  have h2 : (fromComp1 t q 2 : ℕ) = (q 2 : ℕ) := by simp [fromComp1]
  have h3 : (fromComp1 t q 3 : ℕ) = 0 := by simp [fromComp1]
  have h4 : (fromComp1 t q 4 : ℕ) = (q 3 : ℕ) := by simp [fromComp1]
  have h5 : (fromComp1 t q 5 : ℕ) = (q 4 : ℕ) := by simp [fromComp1]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  rw [h0, h1, h2, h3, h4, h5]
  all_goals try { omega }
