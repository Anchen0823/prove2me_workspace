/-
# Cyclically disjoint permutation supports

For a positive order `n`, the additive group `Fin n` supplies `n` permutation
matrices: the graph of `i ↦ i + a` for each shift `a`.  Distinct shifts have no
common matrix cell.  This is the combinatorial input for negative-root arguments
that repeatedly remove disjoint permutation supports from the full board.
-/
import examples.«magic-squares».spencer.SupportSplit

set_option autoImplicit false

open Finset

namespace MagicSquaresSpencer

variable {n : ℕ} [NeZero n]

/-- Translation by `a` in the cyclic additive group `Fin n`. -/
noncomputable def cyclicPerm (a : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.addRight a

theorem cyclicPerm_apply (a i : Fin n) : cyclicPerm a i = i + a := rfl

/-- At a fixed row, two cyclic shifts have the same column only when their
shifts agree. -/
theorem cyclicPerm_shift_injective (i a b : Fin n)
    (h : cyclicPerm a i = cyclicPerm b i) : a = b := by
  rw [cyclicPerm_apply, cyclicPerm_apply] at h
  exact add_left_cancel h

/-- The support of every cyclic permutation matrix contains one cell in every
row, and in particular is nonempty for positive order. -/
theorem cyclicPerm_support_nonempty (a : Fin n) :
    (matSupport (permMatrix (cyclicPerm a))).Nonempty := by
  refine ⟨(0, cyclicPerm a 0), ?_⟩
  exact mem_matSupport_permMatrix_self (cyclicPerm a) 0

/-- The `n` cyclic shifts form pairwise disjoint permutation supports. -/
theorem exists_cyclic_perms_pairwise_disjoint (n : ℕ) [NeZero n] :
    ∃ perms : Fin n → Equiv.Perm (Fin n),
      ∀ i j, i ≠ j →
        Disjoint (matSupport (permMatrix (perms i)))
          (matSupport (permMatrix (perms j))) := by
  refine ⟨fun a => cyclicPerm a, ?_⟩
  intro a b hab
  rw [Finset.disjoint_left]
  intro x hxa hxb
  rw [matSupport_permMatrix] at hxa hxb
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hxa
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hxb
  have hpair : (i, cyclicPerm a i) = (j, cyclicPerm b j) := hi.trans hj.symm
  have hij : i = j := congrArg Prod.fst hpair
  subst j
  have hshift : cyclicPerm a i = cyclicPerm b i := congrArg Prod.snd hpair
  exact hab (cyclicPerm_shift_injective i a b hshift)

/-- The same family, packaged with the usual positive-order hypothesis used by
the semi-magic-square development. -/
theorem exists_cyclic_perms_pairwise_disjoint_of_one_le (n : ℕ) (hn : 1 ≤ n) :
    ∃ perms : Fin n → Equiv.Perm (Fin n),
      ∀ i j, i ≠ j →
        Disjoint (matSupport (permMatrix (perms i)))
          (matSupport (permMatrix (perms j))) := by
  letI : NeZero n := ⟨by omega⟩
  exact exists_cyclic_perms_pairwise_disjoint n

end MagicSquaresSpencer
