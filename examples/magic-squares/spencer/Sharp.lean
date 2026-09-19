/-
# Brick 10: the sharp degree bound — rung S3b

`Recursion.lean` bounds the degree of the level counts by `#B`; aggregating gives degree `≤ n²`.
The sharp bound is `rankB B` — the dimension of the zero-line-sum space of `B` (`Rank.lean`), the
face rank `ρ(B) = |B| - v(B) + c(B)` in disguise — whose maximum over all supports is
`(n - 1)²` (`rankB_univ`).

The induction mirrors `isPolyDegLe_gB` (strong induction on `#B`, the shifted Spencer step), but
the candidates `C ∈ nbSupp B φ` need the degree bound `rankB B - 1`, and `rankB` is **not**
monotone on arbitrary candidates (degenerate candidates can have `rankB C = rankB B`).  Two
facts save it, both provable with the escape lemma `exists_zeroLine_touching`:

* if `C` contains a permutation support, then `rankB C < rankB B` (`rankB_lt_of_candidate`):
  the escape lemma produces a zero-line-sum matrix on `B` that is nonzero on `B \ C`, so
  `zeroLineSubmodule C` is a *proper* subspace of `zeroLineSubmodule B`;
* if `C` contains no permutation, the level counts of `C` vanish identically (Hall), so any
  degree bound holds.

In particular the case `rankB B = 0` (permutation supports and their forced-zero enlargements)
is automatically covered: no candidate contains a permutation (else `rankB C < 0`), so the
recurrence is homogeneous and the counts are constant.

The payoff is `exists_polynomial_semiMagicCount_sharp` — Spencer's theorem with the sharp degree
`(n - 1)²`, still for `t ≥ 1` (the value at `t = 0` is reciprocity, rung S5, not claimed).
Both theorems here are **new** declarations; the published
`isPolyDegLe_gB` / `exists_polynomial_semiMagicCount_pos` are untouched.

Scratch file, built with `lake build examples.«magic-squares».spencer.Sharp`.
-/

import Mathlib
import Definitions.Def_MagicSquares
import examples.«magic-squares».spencer.Rank

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares

variable {n : ℕ}

/-- A sequence that never changes is constant. -/
theorem isPolyDegLe_const_of_succ_eq {b : ℕ → ℚ} (h : ∀ r, b (r + 1) = b r) :
    IsPolyDegLe 0 b := by
  have hb : ∀ r, b r = b 0 := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih => rw [h r, ih]
  refine ⟨Polynomial.C (b 0), by simp, fun r => ?_⟩
  rw [Polynomial.eval_C, hb r]

/-- If no permutation fits inside `B`, the level counts of `B` vanish identically (Hall). -/
theorem gB_eq_zero_of_no_perm (B : Finset (Fin n × Fin n))
    (hno : ∀ σ : Equiv.Perm (Fin n), ¬ matSupport (permMatrix σ) ⊆ B) :
    gB n B = fun _ => (0 : ℚ) := by
  classical
  funext r
  have hcard : (matFiber n (r + 1) (r + 1) B).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro M hM
    rw [matFiber, Finset.mem_filter] at hM
    obtain ⟨-, hls, hsup⟩ := hM
    obtain ⟨σ, hσ⟩ :=
      exists_perm_support_subset_of_lineSums (n := n) (s := r + 1) (by omega) hls
    exact hno σ (by rw [← hsup]; exact hσ)
  show ((matFiber n (r + 1) (r + 1) B).card : ℚ) = 0
  rw [hcard, Nat.cast_zero]

/-- **Spencer's theorem at a fixed support, with the sharp degree.**  The number of `n × n`
squares of line sum `r + 1` whose support is exactly `B` agrees with a polynomial of degree at
most `rankB B` — the zero-line-sum dimension of `B` — at every `r`. -/
theorem isPolyDegLe_gB_sharp (n : ℕ) (B : Finset (Fin n × Fin n)) :
    IsPolyDegLe (rankB B) (gB n B) := by
  classical
  have key : ∀ k, ∀ B : Finset (Fin n × Fin n), B.card = k → IsPolyDegLe (rankB B) (gB n B) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro B hBk
      by_cases hpermB : ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B
      · obtain ⟨σ, hφB⟩ := hpermB
        have hbelow : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)), C ⊂ B := by
          intro C hC
          rw [nbSupp, Finset.mem_erase, mem_fiberCandidates] at hC
          obtain ⟨hne, hCB, -⟩ := hC
          exact Finset.ssubset_iff_subset_ne.mpr ⟨hCB, hne⟩
        have hCsup : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)),
            B \ matSupport (permMatrix σ) ⊆ C := by
          intro C hC
          rw [nbSupp, Finset.mem_erase, mem_fiberCandidates] at hC
          obtain ⟨-, -, hBC⟩ := hC
          exact hBC
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
        by_cases hr0 : rankB B = 0
        · -- `rankB B = 0`: no candidate contains a permutation (else `rankB C < 0`), so the
          -- recurrence is homogeneous and the counts are constant.
          have hz : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)), gB n C = fun _ => (0 : ℚ) := by
            intro C hC
            by_cases hpC : ∃ τ : Equiv.Perm (Fin n), matSupport (permMatrix τ) ⊆ C
            · exfalso
              obtain ⟨τ, hφC⟩ := hpC
              have hlt : rankB C < rankB B :=
                rankB_lt_of_candidate σ τ hφB hφC (hCsup C hC) (hbelow C hC)
              rw [hr0] at hlt
              exact absurd hlt (by norm_num)
            · exact gB_eq_zero_of_no_perm C fun τ h => hpC ⟨τ, h⟩
          rw [hr0]
          refine isPolyDegLe_const_of_succ_eq fun r => ?_
          rw [hrec r, Finset.sum_congr rfl fun C hC => by rw [hz C hC]]
          simp
        · -- `rankB B ≥ 1`: candidates with a permutation get the strict bound, the rest vanish.
          have hpos : 1 ≤ rankB B := Nat.pos_of_ne_zero hr0
          have hih : ∀ C ∈ nbSupp B (matSupport (permMatrix σ)),
              IsPolyDegLe (rankB B - 1) (gB n C) := by
            intro C hC
            by_cases hpC : ∃ τ : Equiv.Perm (Fin n), matSupport (permMatrix τ) ⊆ C
            · obtain ⟨τ, hφC⟩ := hpC
              have hlt : rankB C < rankB B :=
                rankB_lt_of_candidate σ τ hφB hφC (hCsup C hC) (hbelow C hC)
              have hltk : C.card < k := by
                rw [← hBk]
                exact Finset.card_lt_card (hbelow C hC)
              exact isPolyDegLe_mono (ih C.card hltk C rfl) (by omega)
            · rw [gB_eq_zero_of_no_perm C fun τ h => hpC ⟨τ, h⟩]
              exact isPolyDegLe_const 0 (rankB B - 1)
          have hgoal : IsPolyDegLe ((rankB B - 1) + 1) (gB n B) :=
            isPolyDegLe_of_recurrence_succ (b := gB n B) (c := fun C => gB n C)
              (K := rankB B - 1) (nbSupp B (matSupport (permMatrix σ))) hih hrec
          rw [Nat.sub_add_cancel hpos] at hgoal
          exact hgoal
      · -- no permutation fits inside `B`: the counts vanish identically
        rw [gB_eq_zero_of_no_perm B fun σ h => hpermB ⟨σ, h⟩]
        exact isPolyDegLe_const 0 (rankB B)
  exact key B.card B rfl

/-- **Spencer's theorem, sharp.**  For every `t ≥ 1` the number of `n × n` semi-magic squares of
line sum `t` is the value of one fixed polynomial of degree at most `(n - 1) ^ 2`.

Agreement at `t = 0` is *not* claimed — that is the Ehrhart–Macdonald reciprocity statement at
`-1` (rung S5).  This is a **new** declaration; the published
`exists_polynomial_semiMagicCount_pos` (degree `≤ n * n`) is left untouched. -/
theorem exists_polynomial_semiMagicCount_sharp (n : ℕ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ (n - 1) ^ 2 ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  classical
  have hbound : ∀ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset,
      rankB B ≤ (n - 1) ^ 2 := by
    intro B hB
    calc rankB B ≤ rankB (Finset.univ : Finset (Fin n × Fin n)) :=
          rankB_mono (Finset.mem_powerset.mp hB)
      _ = (n - 1) ^ 2 := rankB_univ n
  have hsum : IsPolyDegLe ((n - 1) ^ 2)
      (fun r => ∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, gB n B r) :=
    isPolyDegLe_sum _ fun B hB => isPolyDegLe_mono (isPolyDegLe_gB_sharp n B) (hbound B hB)
  obtain ⟨p, hpdeg, hpval⟩ := exists_poly_comp_X_sub_one hsum
  refine ⟨p, hpdeg, fun t ht => ?_⟩
  rw [hpval t ht, semiMagicCount_eq_sum_matFiber n t]
  push_cast
  refine Finset.sum_congr rfl fun B _ => ?_
  show ((matFiber n ((t - 1) + 1) ((t - 1) + 1) B).card : ℚ) = ((matFiber n t t B).card : ℚ)
  rw [Nat.sub_add_cancel ht]

end MagicSquaresSpencer
