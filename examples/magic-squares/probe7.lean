import Mathlib
#check Fin.forall_fin_three
#check Fin.forall_fin_succ
#check Fin.forall_fin_two
example (P : Fin 3 → Prop) [DecidablePred P] : (∀ i : Fin 3, P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  simp [Fin.forall_fin_three]
