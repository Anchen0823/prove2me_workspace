/-
# Brick 4: splitting a semi-magic square along a permutation in its support

This is the technical heart of step 3 of Spencer's proof.  Given a semi-magic square `T` of
line sum `r` and a permutation `σ` whose support `φ = {(i, σ i)}` lies inside the support of `T`,
the matrix `S := T - P` (where `P` is the 0/1 matrix of `σ`) is again semi-magic, now of line
sum `r - 1`, and its support is obtained from that of `T` by deleting exactly those cells of `φ`
where `T` takes the value `1`:

  `supp S ∪ φ = supp T`,   `(i, σ i) ∈ supp S ↔ 1 < T i (σ i)`.

Equivalently, `supp S` runs over the support sets `C` with `supp T \ φ ⊆ C ⊆ supp T`, and
`C = supp T` exactly when `T ≥ 2` on `φ`.  Since `S ↦ S + P` inverts `T ↦ T - P`, this is a
bijection and produces the recurrence consumed by `isPolyDegLe_of_recurrence`:

  `h_B(r) = h_B(r-1) + Σ_{C : B \ φ ⊆ C ⊊ B} h_C(r-1)`   for `r ≥ 2`.

`0 < T i (σ i)` (i.e. `φ ⊆ supp T`) is what makes `T - P` a genuine subtraction; positivity of
the line sum is what makes `φ` exist at all (see `HallSupport.lean`).

Scratch file, compiled with `lake env lean`.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000

open Finset

namespace MagicSquaresSpencer

variable {n : ℕ}

/-- The `0/1` matrix of a permutation. -/
def permMatrix (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if σ i = j then 1 else 0

/-- The support of a matrix, as a finset of positions. -/
def matSupport (M : Matrix (Fin n) (Fin n) ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => 0 < M p.1 p.2

theorem permMatrix_apply (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permMatrix σ i j = if σ i = j then 1 else 0 := rfl

/-- `P ≤ T` entrywise as soon as `T` is positive on the support of `σ`. -/
theorem permMatrix_le_of_pos (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) : ∀ i j, permMatrix σ i j ≤ T i j := by
  intro i j
  by_cases h : σ i = j
  · rw [permMatrix_apply, if_pos h, ← h]
    exact hσ i
  · rw [permMatrix_apply, if_neg h]
    exact Nat.zero_le _

theorem permMatrix_row (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ∑ j : Fin n, permMatrix σ i j = 1 := by
  have h : ∀ j : Fin n, permMatrix σ i j = if σ i = j then (1 : ℕ) else 0 := fun j => rfl
  simp only [h]
  rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin n)) (σ i) fun _ => (1 : ℕ)]
  simp

/-- The permutation matrix is transposed by passing to the inverse permutation. -/
theorem permMatrix_comm (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permMatrix σ i j = permMatrix σ.symm j i := by
  rw [permMatrix_apply, permMatrix_apply]
  by_cases h : σ i = j
  · rw [if_pos h, if_pos (by rw [← h, σ.symm_apply_apply])]
  · rw [if_neg h, if_neg fun h' => h (by rw [← h', σ.apply_symm_apply])]

theorem permMatrix_col (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    ∑ i : Fin n, permMatrix σ i j = 1 := by
  rw [Finset.sum_congr rfl fun i _ => permMatrix_comm σ i j]
  exact permMatrix_row σ.symm j

theorem matSupport_add (A B : Matrix (Fin n) (Fin n) ℕ) :
    matSupport (A + B) = matSupport A ∪ matSupport B := by
  ext p
  obtain ⟨i, j⟩ := p
  have h : (A + B) i j = A i j + B i j := Matrix.add_apply A B i j
  simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, h]
  omega

theorem matSupport_permMatrix (σ : Equiv.Perm (Fin n)) :
    matSupport (permMatrix σ) = Finset.univ.image fun i => (i, σ i) := by
  ext p
  obtain ⟨i, j⟩ := p
  rw [Finset.mem_image]
  constructor
  · intro h
    simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have h' : σ i = j := by
      by_contra hne
      rw [permMatrix_apply, if_neg hne] at h
      exact absurd h (by norm_num)
    exact ⟨i, Finset.mem_univ i, by rw [h']⟩
  · rintro ⟨k, -, hk⟩
    simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    have hki : k = i := (Prod.ext_iff.mp hk).1
    subst hki
    have hkj : σ k = j := (Prod.ext_iff.mp hk).2
    rw [permMatrix_apply, if_pos hkj]
    norm_num

/-- **The split.**  Removing the permutation matrix from a square that is positive on its support
yields a square whose support is that of the original, minus the cells of the permutation where
the original entry is exactly `1`. -/
theorem matSupport_sub_permMatrix_union (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) :
    matSupport (T - permMatrix σ) ∪ matSupport (permMatrix σ) = matSupport T := by
  ext p
  obtain ⟨i, j⟩ := p
  have hsub : (T - permMatrix σ) i j = T i j - permMatrix σ i j := Matrix.sub_apply T _ i j
  have hpm : permMatrix σ i j = if σ i = j then 1 else 0 := rfl
  simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    hsub, hpm]
  by_cases h : σ i = j
  · rw [if_pos h]
    constructor
    · intro _
      rw [← h]
      exact hσ i
    · intro _
      exact Or.inr (by norm_num)
  · rw [if_neg h]
    constructor
    · rintro (h1 | h2)
      · rwa [Nat.sub_zero] at h1
      · exact absurd h2 (by norm_num)
    · intro hT
      exact Or.inl (by rwa [Nat.sub_zero])

theorem matSupport_sub_permMatrix_subset (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) : matSupport (T - permMatrix σ) ⊆ matSupport T := by
  intro p hp
  rw [← matSupport_sub_permMatrix_union T σ hσ]
  exact Finset.mem_union_left _ hp

/-- A cell of the permutation survives the split exactly when the original entry exceeds `1`. -/
theorem mem_matSupport_sub_permMatrix_perm (T : Matrix (Fin n) (Fin n) ℕ)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (i, σ i) ∈ matSupport (T - permMatrix σ) ↔ 1 < T i (σ i) := by
  have hsub : (T - permMatrix σ) i (σ i) = T i (σ i) - permMatrix σ i (σ i) :=
    Matrix.sub_apply T _ i (σ i)
  have hpm : permMatrix σ i (σ i) = 1 := by rw [permMatrix_apply, if_pos rfl]
  simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and, hsub, hpm]
  omega

theorem sub_add_permMatrix (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) : T - permMatrix σ + permMatrix σ = T := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have := permMatrix_le_of_pos T σ hσ i j
  omega

theorem add_sub_permMatrix (S : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n)) :
    S + permMatrix σ - permMatrix σ = S := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  exact Nat.add_sub_cancel _ _

theorem sum_sub_permMatrix (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) (i : Fin n) :
    ∑ j : Fin n, (T - permMatrix σ) i j = (∑ j : Fin n, T i j) - 1 := by
  have key : ∑ j : Fin n, T i j = (∑ j : Fin n, (T - permMatrix σ) i j) + 1 := by
    have h : ∀ j : Fin n, T i j = (T - permMatrix σ) i j + permMatrix σ i j := by
      intro j
      rw [Matrix.sub_apply, Nat.sub_add_cancel (permMatrix_le_of_pos T σ hσ i j)]
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, permMatrix_row σ i]
  omega

theorem sum_sub_permMatrix_col (T : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, 0 < T i (σ i)) (j : Fin n) :
    ∑ i : Fin n, (T - permMatrix σ) i j = (∑ i : Fin n, T i j) - 1 := by
  have key : ∑ i : Fin n, T i j = (∑ i : Fin n, (T - permMatrix σ) i j) + 1 := by
    have h : ∀ i : Fin n, T i j = (T - permMatrix σ) i j + permMatrix σ i j := by
      intro i
      rw [Matrix.sub_apply, Nat.sub_add_cancel (permMatrix_le_of_pos T σ hσ i j)]
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, permMatrix_col σ j]
  omega

/-! ## Bricks 5-6: boxes, fibres, and the fibres of the split

The counting functions of the Spencer recursion live on matrices **with entries bounded by the
line sum**, and the bound drops by one when the permutation is removed.  It is therefore
convenient to describe a fibre as a finset of `ℕ`-valued matrices cut out by an explicit bound
condition, rather than as a finset of the platform's `Fin (t+1)`-valued matrices: the level-`s`
and level-`(s-1)` fibres then live in the *same* type, which is what makes the bijection
`T ↦ T - P` statable at all.  (With `Fin`-valued entries the two levels are different types, and
`Fin` subtraction moreover wraps around.)

The bridge back to the platform's `semiMagicCount` is a single cardinality lemma, deferred.
-/

/-- All `n × n` matrices of natural numbers with entries at most `s`. -/
def matBox (n s : ℕ) : Finset (Matrix (Fin n) (Fin n) ℕ) :=
  Finset.map
    ⟨fun M : Matrix (Fin n) (Fin n) (Fin (s + 1)) => fun i j => (M i j : ℕ),
      fun A B h => by funext i j; exact Fin.ext (congrFun (congrFun h i) j)⟩
    Finset.univ

theorem mem_matBox {n s : ℕ} {M : Matrix (Fin n) (Fin n) ℕ} :
    M ∈ matBox n s ↔ ∀ i j, M i j ≤ s := by
  constructor
  · intro h
    rw [matBox, Finset.mem_map] at h
    obtain ⟨M', -, hM'⟩ := h
    intro i j
    rw [← congrFun (congrFun hM' i) j]
    exact Nat.le_of_lt_succ (M' i j).isLt
  · intro h
    rw [matBox, Finset.mem_map]
    refine ⟨fun i j => ⟨M i j, Nat.lt_succ_of_le (h i j)⟩, Finset.mem_univ _, ?_⟩
    funext i j
    rfl

theorem matBox_mono {n s t : ℕ} (h : s ≤ t) : matBox n s ⊆ matBox n t := by
  intro M hM
  rw [mem_matBox] at hM ⊢
  exact fun i j => (hM i j).trans h

/-- A matrix all of whose rows and columns sum to `s`. -/
def LineSums (M : Matrix (Fin n) (Fin n) ℕ) (s : ℕ) : Prop :=
  (∀ i, ∑ j, M i j = s) ∧ ∀ j, ∑ i, M i j = s

/-- The matrices with entries at most `m`, line sums `s` and support exactly `B`. -/
noncomputable def matFiber (n m s : ℕ) (B : Finset (Fin n × Fin n)) :
    Finset (Matrix (Fin n) (Fin n) ℕ) := by
  classical
  exact (matBox n m).filter fun M => LineSums M s ∧ matSupport M = B

/-- In a matrix whose rows all sum to `s`, every entry is at most `s`. -/
theorem le_of_rowSum {n s : ℕ} {M : Matrix (Fin n) (Fin n) ℕ} (h : ∀ i, ∑ j, M i j = s)
    (i j : Fin n) : M i j ≤ s := by
  have := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n))) (f := fun j => M i j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [h i] at this
  exact this

/-- Removing a permutation matrix from a square keeps the entries within the bound `s`, and the
line sums drop by one; in fact the entries drop to at most `s - 1`. -/
theorem matBox_sub_permMatrix {n s : ℕ} {T : Matrix (Fin n) (Fin n) ℕ}
    (σ : Equiv.Perm (Fin n)) (hrow : ∀ i, ∑ j, (T - permMatrix σ) i j = s - 1) :
    T - permMatrix σ ∈ matBox n (s - 1) := by
  rw [mem_matBox]
  intro i j
  exact le_of_rowSum hrow i j

theorem sum_add_permMatrix (S : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ∑ j : Fin n, (S + permMatrix σ) i j = (∑ j : Fin n, S i j) + 1 := by
  have h : ∀ j : Fin n, (S + permMatrix σ) i j = S i j + permMatrix σ i j :=
    fun j => Matrix.add_apply S _ i j
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, permMatrix_row σ i]

theorem sum_add_permMatrix_col (S : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (j : Fin n) :
    ∑ i : Fin n, (S + permMatrix σ) i j = (∑ i : Fin n, S i j) + 1 := by
  have h : ∀ i : Fin n, (S + permMatrix σ) i j = S i j + permMatrix σ i j :=
    fun i => Matrix.add_apply S _ i j
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, permMatrix_col σ j]

theorem permMatrix_le_one (σ : Equiv.Perm (Fin n)) (i j : Fin n) : permMatrix σ i j ≤ 1 := by
  rw [permMatrix_apply]
  split_ifs <;> omega

/-- Adding the permutation matrix back keeps the entries within the bound `s`. -/
theorem mem_matBox_add_permMatrix {n s : ℕ} (hs : 1 ≤ s) {S : Matrix (Fin n) (Fin n) ℕ}
    (hrow : ∀ i, ∑ j, S i j = s - 1) (σ : Equiv.Perm (Fin n)) :
    S + permMatrix σ ∈ matBox n s := by
  rw [mem_matBox]
  intro i j
  have h1 : S i j ≤ s - 1 := le_of_rowSum hrow i j
  have h2 : permMatrix σ i j ≤ 1 := permMatrix_le_one σ i j
  rw [Matrix.add_apply]
  omega

/-- If `A ⊆ B`, `C ⊆ B` and `B \ A ⊆ C`, then `C ∪ A = B`. -/
theorem union_eq_of_subset {α : Type*} [DecidableEq α] {A B C : Finset α}
    (hCB : C ⊆ B) (hAB : A ⊆ B) (hB : B \ A ⊆ C) : C ∪ A = B := by
  ext x
  rw [Finset.mem_union]
  constructor
  · rintro (hx | hx)
    · exact hCB hx
    · exact hAB hx
  · intro hx
    by_cases hxA : x ∈ A
    · exact Or.inr hxA
    · exact Or.inl (hB (Finset.mem_sdiff.mpr ⟨hx, hxA⟩))

theorem mem_matSupport_permMatrix_self (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (i, σ i) ∈ matSupport (permMatrix σ) := by
  rw [matSupport_permMatrix]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- The candidate supports for the split of a square supported on `B` along a permutation with
support `φ`: the `C` with `B \ φ ⊆ C ⊆ B`. -/
noncomputable def fiberCandidates (B φ : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) := by
  classical
  exact B.powerset.filter fun C => B \ φ ⊆ C

theorem mem_fiberCandidates {B φ C : Finset (Fin n × Fin n)} :
    C ∈ fiberCandidates B φ ↔ C ⊆ B ∧ B \ φ ⊆ C := by
  classical
  simp [fiberCandidates]

/-- **The heart of Spencer's step 3.**  Subtracting the permutation matrix spreads the squares of
line sum `s` whose support is `B` bijectively over the squares of line sum `s - 1` whose support
`C` satisfies `B \ φ ⊆ C ⊆ B`. -/
theorem card_matFiber_split {n s : ℕ} (hs : 1 ≤ s) {B : Finset (Fin n × Fin n)}
    (σ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B) :
    (matFiber n s s B).card
      = ∑ C ∈ fiberCandidates B (matSupport (permMatrix σ)), (matFiber n s (s - 1) C).card := by
  classical
  have hbij : (matFiber n s s B).card
      = ((fiberCandidates B (matSupport (permMatrix σ))).sigma
          fun C => matFiber n s (s - 1) C).card := by
    refine Finset.card_bij (fun T _ => ⟨matSupport (T - permMatrix σ), T - permMatrix σ⟩) ?_ ?_ ?_
    · rintro T hT
      simp only [matFiber, Finset.mem_filter] at hT
      obtain ⟨hbox, hls, hsup⟩ := hT
      have hσ : ∀ i, 0 < T i (σ i) := by
        intro i
        have hmem : (i, σ i) ∈ matSupport T := by
          rw [hsup]
          exact hφB (mem_matSupport_permMatrix_self σ i)
        simpa [matSupport] using hmem
      have hunion := matSupport_sub_permMatrix_union T σ hσ
      have hsub : matSupport (T - permMatrix σ) ⊆ B := by
        intro x hx
        rw [← hsup, ← hunion]
        exact Finset.mem_union_left _ hx
      have hsdiff : B \ matSupport (permMatrix σ) ⊆ matSupport (T - permMatrix σ) := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        have hone : x ∈ matSupport (T - permMatrix σ) ∪ matSupport (permMatrix σ) := by
          rw [hunion, hsup]
          exact hx.1
        rcases Finset.mem_union.mp hone with h | h
        · exact h
        · exact absurd h hx.2
      rw [Finset.mem_sigma, mem_fiberCandidates]
      refine ⟨⟨hsub, hsdiff⟩, ?_⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_, rfl⟩
      · rw [mem_matBox] at hbox ⊢
        intro i j
        show (T - permMatrix σ) i j ≤ s
        rw [Matrix.sub_apply]
        have hTij : T i j ≤ s := hbox i j
        have hle := permMatrix_le_of_pos T σ hσ i j
        omega
      · exact ⟨fun i => by rw [sum_sub_permMatrix T σ hσ i, hls.1 i],
               fun j => by rw [sum_sub_permMatrix_col T σ hσ j, hls.2 j]⟩
    · rintro T₁ hT₁ T₂ hT₂ heq
      simp only [matFiber, Finset.mem_filter] at hT₁ hT₂
      have hσ₁ : ∀ i, 0 < T₁ i (σ i) := by
        intro i
        have hmem : (i, σ i) ∈ matSupport T₁ := by
          rw [hT₁.2.2]
          exact hφB (mem_matSupport_permMatrix_self σ i)
        simpa [matSupport] using hmem
      have hσ₂ : ∀ i, 0 < T₂ i (σ i) := by
        intro i
        have hmem : (i, σ i) ∈ matSupport T₂ := by
          rw [hT₂.2.2]
          exact hφB (mem_matSupport_permMatrix_self σ i)
        simpa [matSupport] using hmem
      have h : T₁ - permMatrix σ = T₂ - permMatrix σ := congrArg Sigma.snd heq
      rw [← sub_add_permMatrix T₁ σ hσ₁, ← sub_add_permMatrix T₂ σ hσ₂, h]
    · rintro ⟨C, S⟩ hmem
      rw [Finset.mem_sigma, mem_fiberCandidates] at hmem
      obtain ⟨⟨hCB, hsdiff⟩, hS⟩ := hmem
      simp only [matFiber, Finset.mem_filter] at hS
      obtain ⟨hSbox, hSls, hSsup⟩ := hS
      refine ⟨S + permMatrix σ, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
        · exact mem_matBox_add_permMatrix hs hSls.1 σ
        · exact ⟨fun i => by rw [sum_add_permMatrix S σ i, hSls.1 i]; omega,
                 fun j => by rw [sum_add_permMatrix_col S σ j, hSls.2 j]; omega⟩
        · rw [matSupport_add, hSsup, union_eq_of_subset hCB hφB hsdiff]
      · rw [add_sub_permMatrix S σ, hSsup]
  rw [hbij, Finset.card_sigma]

/-- **The recurrence.**  For `s ≥ 1` the number of squares of line sum `s` with support `B`
equals the number of line sum `s - 1` still supported on `B`, plus the sum over the strictly
smaller candidates `C`. -/
theorem card_matFiber_recurrence {n s : ℕ} (hs : 1 ≤ s) {B : Finset (Fin n × Fin n)}
    (σ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B) :
    (matFiber n s s B).card
      = (matFiber n s (s - 1) B).card
        + ∑ C ∈ (fiberCandidates B (matSupport (permMatrix σ))).erase B,
            (matFiber n s (s - 1) C).card := by
  classical
  have hBmem : B ∈ fiberCandidates B (matSupport (permMatrix σ)) := by
    rw [mem_fiberCandidates]
    exact ⟨Finset.Subset.refl B, Finset.sdiff_subset⟩
  rw [card_matFiber_split hs σ hφB]
  rw [← Finset.sum_erase_add (s := fiberCandidates B (matSupport (permMatrix σ)))
    (f := fun C => (matFiber n s (s - 1) C).card) hBmem, add_comm]

end MagicSquaresSpencer
