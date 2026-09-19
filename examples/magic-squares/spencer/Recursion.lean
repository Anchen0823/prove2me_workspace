/-
# Brick 7: the support-set recursion, and polynomiality of the level counts

This is the last piece of Spencer's step 3 (`SPENCER-ROUTE.md` §5, rung **S2d**).  `SupportSplit.lean`
produced the recurrence one level at a time,

  `#(fibre of line sum s at B) = #(fibre of line sum s-1 at B) + Σ_{C ∈ nb B φ} #(fibre of line sum s-1 at C)`,

but with the *ambient* bound (the box the entries live in) still written as `s` on both sides, and
with the permutation `σ` left free.  Three things are done here:

1. **Cancelling the ambient bound.**  A fibre of line sum `s` already has all entries `≤ s`, so the
   ambient bound is redundant as soon as it dominates the line sum (`matFiber_eq_of_le`).  This is
   what lets the two sides live in the same type at all.
2. **Choosing the permutation.**  Hall (`HallSupport.lean`) gives a permutation inside the support of
   any square of *positive* line sum (`exists_perm_support_subset_of_lineSums`).  Note that once
   `φ(σ) ⊆ B = supp T`, the split applies to `T` for free: the hypothesis `0 < T i (σ i)` needed by
   `SupportSplit.lean` is automatic.  So a single `σ` per support set serves *every* line sum, which
   is exactly what a recurrence with constant coefficients requires.
3. **The induction.**  Shifting once (`gB n B r := #(fibre of line sum r+1 at B)`) turns the
   recurrence into `gB (r+1) = gB r + Σ_C gB C r`, the shifted Spencer step, and strong induction on
   `B.card` — legitimate because every `C ∈ nb B φ` is a *strict* subset of `B` — closes it.

The conclusion is

  `IsPolyDegLe B.card (gB n B)`  for every support `B`,

i.e. the count of squares of line sum `t ≥ 1` with support exactly `B` is a polynomial in `t` of
degree at most `#B`.  Summing over the supports (rung S4) is deliberately *not* attempted here.

Scratch file, built with `lake build examples.«magic-squares».spencer.Recursion`.
-/
import examples.«magic-squares».spencer.Spencer
import examples.«magic-squares».spencer.HallSupport
import examples.«magic-squares».spencer.SupportSplit

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial


/-! ## Step 1: the ambient bound is redundant

`matFiber n m s B` carries both the ambient bound `m` and the line sum `s`.  As soon as `s ≤ m` the
bound `m` is implied by the line sum, so the fibre does not depend on it.  This is the cancellation
promised in `card_matFiber_recurrence`: with it, both sides of the recurrence can be written with the
ambient bound equal to the line sum, which is the form the shift wants. -/

theorem matFiber_eq_of_le {n m s : ℕ} (h : s ≤ m) (B : Finset (Fin n × Fin n)) :
    matFiber n m s B = matFiber n s s B := by
  classical
  ext M
  simp only [matFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hbox, hls, hsup⟩
    rw [mem_matBox] at hbox ⊢
    exact ⟨fun i j => le_of_rowSum hls.1 i j, hls, hsup⟩
  · rintro ⟨hbox, hls, hsup⟩
    rw [mem_matBox] at hbox ⊢
    exact ⟨fun i j => (hbox i j).trans h, hls, hsup⟩


/-! ## Step 2: Hall, in the shape the recursion consumes -/

/-- **The permutation inside a support.**  A square of positive line sum has a permutation inside
its support.  This is `exists_perm_pos_of_line_sums` rewritten in terms of `matSupport`, and it is
all the freedom the recursion needs: a permutation supported on `B` splits *every* square supported
on `B`, at every line sum. -/
theorem exists_perm_support_subset_of_lineSums {n s : ℕ} (hs : 1 ≤ s)
    {T : Matrix (Fin n) (Fin n) ℕ} (hls : LineSums T s) :
    ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ matSupport T := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_pos_of_line_sums T (by omega) hls.1 hls.2
  refine ⟨σ, ?_⟩
  rw [matSupport_permMatrix]
  intro p hp
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
  simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hσ i


/-! ## Step 3: the recurrence with the bound cancelled, and the induction -/

/-- The supports strictly below `B` that the split along a permutation with support `φ` can produce:
the `C` with `B \ φ ⊆ C ⊆ B`, `C ≠ B`. -/
noncomputable def nbSupp {n : ℕ} (B φ : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) :=
  (fiberCandidates B φ).erase B

/-- **The recurrence, ready for the Spencer step.**  For a square of line sum `s + 1` supported on
`B` and a permutation supported inside `B`, the level-`(s+1)` fibre at `B` splits into the level-`s`
fibre at `B` and the level-`s` fibres at the strictly smaller supports of `nbSupp B φ`. -/
theorem card_matFiber_recurrence_succ {n s : ℕ} {B : Finset (Fin n × Fin n)}
    (σ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B) :
    (matFiber n (s + 1) (s + 1) B).card
      = (matFiber n s s B).card
        + ∑ C ∈ nbSupp B (matSupport (permMatrix σ)), (matFiber n s s C).card := by
  classical
  have h := card_matFiber_recurrence (n := n) (s := s + 1) (B := B) (by omega) σ hφB
  have hsub : s + 1 - 1 = s := by omega
  rw [hsub] at h
  rw [matFiber_eq_of_le (m := s + 1) (Nat.le_succ s) B] at h
  rw [Finset.sum_congr rfl
    (fun C _ => congrArg Finset.card (matFiber_eq_of_le (m := s + 1) (Nat.le_succ s) C))] at h
  simpa only [nbSupp] using h

/-- The number of squares of line sum `r + 1` with support exactly `B`, as a sequence in `r`.

The `+ 1` is the shift of `SPENCER-ROUTE.md` §4.1: the support recursion only sees *positive* line
sums, and after shifting away from line sum `0` it is homogeneous with the constants as its base
case, so the Spencer step applies with no exceptional first coefficient.  The price is that the
resulting polynomial agrees with the true count only for `t ≥ 1`; the value at `t = 0` is the
reciprocity statement (rung S5) and is not claimed here. -/
noncomputable def gB (n : ℕ) (B : Finset (Fin n × Fin n)) : ℕ → ℚ :=
  fun r => ((matFiber n (r + 1) (r + 1) B).card : ℚ)

/-- In dimension `0` there is exactly one matrix, and it lies in the fibre over the empty support at
every level: the line-sum equations are vacuous, so nothing forces it out. -/
theorem card_matFiber_zero (m s : ℕ) : (matFiber 0 m s (∅ : Finset (Fin 0 × Fin 0))).card = 1 := by
  classical
  let M0 : Matrix (Fin 0) (Fin 0) ℕ := fun i => i.elim0
  have huniq : ∀ M : Matrix (Fin 0) (Fin 0) ℕ, M = M0 := fun M => funext fun i => i.elim0
  have hmem : ∀ M : Matrix (Fin 0) (Fin 0) ℕ, M ∈ matFiber 0 m s ∅ := by
    intro M
    rw [huniq M, matFiber, Finset.mem_filter]
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · rw [mem_matBox]
      intro i
      exact i.elim0
    · exact ⟨fun i => i.elim0, fun j => j.elim0⟩
    · exact Finset.eq_empty_iff_forall_notMem.mpr fun p _ => p.1.elim0
  refine Finset.card_eq_one.mpr ⟨M0, ?_⟩
  exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem M0, fun M _ => huniq M⟩

/-- The empty support contributes a *constant*: the level-`(r+1)` fibre over `∅` is empty for
`n ≥ 1` (a matrix of support `∅` is zero, and its line sums are `0`), and a single point for
`n = 0`, where the line-sum equations are vacuous. -/
theorem isPolyDegLe_gB_empty (n : ℕ) : IsPolyDegLe 0 (gB n (∅ : Finset (Fin n × Fin n))) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    refine ⟨Polynomial.C 1, by simp, fun r => ?_⟩
    show (Polynomial.C (1 : ℚ)).eval (r : ℚ) = ((matFiber 0 (r + 1) (r + 1) ∅).card : ℚ)
    rw [Polynomial.eval_C, card_matFiber_zero]
    norm_num
  · refine ⟨Polynomial.C 0, by simp, fun r => ?_⟩
    rw [Polynomial.eval_C]
    have hcard : (matFiber n (r + 1) (r + 1) (∅ : Finset (Fin n × Fin n))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro M hM
      rw [matFiber, Finset.mem_filter] at hM
      obtain ⟨-, hls, hsup⟩ := hM
      have hM0 : ∀ j : Fin n, M ⟨0, hn1⟩ j = 0 := by
        intro j
        by_contra hne
        have hmem : (⟨0, hn1⟩, j) ∈ matSupport M := by
          simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Nat.pos_of_ne_zero hne
        rw [hsup] at hmem
        simp at hmem
      have hpos : (0 : ℕ) = r + 1 := by
        rw [← hls.1 ⟨0, hn1⟩]
        exact (Finset.sum_eq_zero fun j _ => hM0 j).symm
      omega
    show (0 : ℚ) = ((matFiber n (r + 1) (r + 1) (∅ : Finset (Fin n × Fin n))).card : ℚ)
    rw [hcard, Nat.cast_zero]

/-- **Spencer's theorem at a fixed support.**  The number of `n × n` semi-magic squares of line sum
`r + 1` whose support is exactly `B` is a polynomial in `r` of degree at most `#B`.

The proof is strong induction on `#B`.  If no permutation fits inside `B`, the fibre is *empty* at
every level (Hall), so the sequence is zero.  Otherwise fix one such permutation `σ` — it serves
every level — and apply the shifted Spencer step to `card_matFiber_recurrence_succ`; the sum runs
over strict subsets, which is what makes the induction legitimate. -/
theorem isPolyDegLe_gB (n : ℕ) (B : Finset (Fin n × Fin n)) :
    IsPolyDegLe B.card (gB n B) := by
  classical
  have key : ∀ k, ∀ B : Finset (Fin n × Fin n), B.card = k → IsPolyDegLe B.card (gB n B) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro B hBk
      by_cases hB0 : B = ∅
      · subst hB0
        rw [Finset.card_empty]
        exact isPolyDegLe_gB_empty n
      · have hBpos : 1 ≤ B.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hB0)
        by_cases hno : ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B
        · obtain ⟨σ, hφB⟩ := hno
          have hbelow : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)), C ⊂ B := by
            intro C hC
            rw [nbSupp, Finset.mem_erase, mem_fiberCandidates] at hC
            obtain ⟨hne, hCB, -⟩ := hC
            exact Finset.ssubset_iff_subset_ne.mpr ⟨hCB, hne⟩
          have hih : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)),
              IsPolyDegLe (B.card - 1) (gB n C) := by
            intro C hC
            have hlt := hbelow C hC
            have hcard : C.card ≤ B.card - 1 := by
              have := Finset.card_lt_card hlt
              omega
            have hltk : C.card < k := by
              rw [← hBk]
              exact Finset.card_lt_card hlt
            exact isPolyDegLe_mono (ih C.card hltk C rfl) hcard
          have hrec : ∀ r : ℕ, gB n B (r + 1)
              = gB n B r + ∑ C ∈ nbSupp B (matSupport (permMatrix σ)), gB n C r := by
            intro r
            have hstep := card_matFiber_recurrence_succ (n := n) (s := r + 1) (B := B) σ hφB
            change ((matFiber n (r + 1 + 1) (r + 1 + 1) B).card : ℚ)
                = ((matFiber n (r + 1) (r + 1) B).card : ℚ)
                  + ∑ C ∈ nbSupp B (matSupport (permMatrix σ)),
                      ((matFiber n (r + 1) (r + 1) C).card : ℚ)
            rw [hstep]
            push_cast
            rfl
          have hgoal : IsPolyDegLe ((B.card - 1) + 1) (gB n B) :=
            isPolyDegLe_of_recurrence_succ (b := gB n B) (c := fun C => gB n C)
              (K := B.card - 1) (nbSupp B (matSupport (permMatrix σ))) hih hrec
          rw [Nat.sub_add_cancel hBpos] at hgoal
          exact hgoal
        · -- no permutation fits inside `B`: Hall says the fibre is empty at every positive level
          have hzero : gB n B = fun _ => (0 : ℚ) := by
            funext r
            have hcard : (matFiber n (r + 1) (r + 1) B).card = 0 := by
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
              intro M hM
              rw [matFiber, Finset.mem_filter] at hM
              obtain ⟨-, hls, hsup⟩ := hM
              obtain ⟨σ, hσ⟩ :=
                exists_perm_support_subset_of_lineSums (n := n) (s := r + 1) (by omega) hls
              exact hno ⟨σ, by rw [← hsup]; exact hσ⟩
            show ((matFiber n (r + 1) (r + 1) B).card : ℚ) = 0
            rw [hcard, Nat.cast_zero]
          rw [hzero]
          exact isPolyDegLe_const 0 B.card
  exact key B.card B rfl

end MagicSquaresSpencer
