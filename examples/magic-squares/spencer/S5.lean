/-
# Brick 12 (rung S5): the value at line sum `0`, reduced to a finite identity

`Recursion.lean` produces a polynomial for every support, but only for line sums `t ≥ 1`; the
missing point is `t = 0`.  This brick makes the obstruction exact and *polynomial-free*.

Write

* `qB n B` for the polynomial with `qB n B r = #(squares of line sum r + 1 with support exactly B)`
  (degree at most `#B`, from `isPolyDegLe_gB`),
* `sB n B := qB n B (-1)` for its value one step below line sum `0`.

Two facts are proved here, entirely inside `ℚ[X]` and `ℕ`:

* the **difference equation**  `qB (X + 1) - qB = Σ_{C ∈ nbOf n B} qB C`,  where `nbOf n B` is the
  neighbour set of the split (`empty` when no permutation fits inside `B`, so that the identity
  holds at *every* `B`, support or not);
* evaluating it at `X = -1` gives the **recursion**  `sB n B = #(level-1 fibre at B) - Σ_C sB n C`,
  in which no polynomial occurs any more.

Consequently rung S5 (`p(0) = 1`, i.e. the count is polynomial at `t = 0` too) is equivalent to the
single numerical statement

  `Σ_{B a support} sB n B = 1`,

and *that* follows from the two inputs isolated at the end of the file:

* **(A)** `sB n B = (-1) ^ rankB B` for every support — Ehrhart–Macdonald reciprocity at `-1`;
* **(B)** `Σ_{B a support} (-1) ^ rankB B = 1` — Euler's formula for the face lattice of the
  Birkhoff polytope, which contains no Ehrhart theory at all.

Both are numerical facts about finitely many supports of a fixed `n`; neither is proved here.  What
*is* proved here is that they are exactly what is missing: `exists_polynomial_semiMagicCount_…`
below turns either statement into the mission's goal.  See `missions/magic-squares-v/S5-NOTES.md`
for the analysis and the (exact-arithmetic) verification for `n ≤ 4`.

Built with `lake build SpencerRoute`.
-/

import examples.«magic-squares».spencer.Sharp

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares


/-! ## Step 0: polynomials that vanish on `ℕ` (or on the positive integers) -/

/-- A polynomial over `ℚ` which vanishes at every natural number vanishes identically.  This is the
only place where the route needs a fact about `ℚ[X]` rather than about sequences, and it is what
converts a recurrence in `t : ℕ` into an identity of polynomials. -/
theorem poly_eq_zero_of_nat_eval_eq_zero {p : Polynomial ℚ} (h : ∀ r : ℕ, p.eval (r : ℚ) = 0) :
    p = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot p ?_
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (f := fun r : ℕ => (r : ℚ))
    Nat.cast_injective)
  rintro x ⟨r, rfl⟩
  exact h r

/-- The same, for a polynomial vanishing only on the *positive* integers: it vanishes identically.
Multiplying by `X` (which is not a zero divisor) shifts the positive integers down to `ℕ`. -/
theorem poly_eq_zero_of_pos_eval_eq_zero {p : Polynomial ℚ}
    (h : ∀ r : ℕ, 1 ≤ r → p.eval (r : ℚ) = 0) : p = 0 := by
  have hX : X * p = 0 := by
    refine poly_eq_zero_of_nat_eval_eq_zero fun r => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_X]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      rw [Nat.cast_zero, zero_mul]
    · rw [h r hr, mul_zero]
  rcases mul_eq_zero.mp hX with h' | h'
  · exact absurd h' Polynomial.X_ne_zero
  · exact h'


/-! ## Step 1: the empty support, and the count at line sum `0` -/

/-- For `n ≥ 1` there is no matrix of positive line sum with empty support: every entry vanishes, so
every row sums to `0`.  This is the *reason* the support recursion stops at line sum `1`, and the
reason the empty support is excluded from `IsSupport` below. -/
theorem card_matFiber_empty {n m s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s) :
    (matFiber n m s (∅ : Finset (Fin n × Fin n))).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro M hM
  rw [matFiber, Finset.mem_filter] at hM
  obtain ⟨-, hls, hsup⟩ := hM
  have hzero : ∀ j : Fin n, M ⟨0, hn⟩ j = 0 := by
    intro j
    by_contra hne
    have hmem : (⟨0, hn⟩, j) ∈ matSupport M := by
      simp only [matSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.pos_of_ne_zero hne
    rw [hsup] at hmem
    simp at hmem
  have hrow := hls.1 ⟨0, hn⟩
  rw [Finset.sum_eq_zero fun j _ => hzero j] at hrow
  omega

/-- Line sum `0` has exactly one semi-magic square: the zero matrix. -/
theorem semiMagicCount_zero (n : ℕ) : semiMagicCount n 0 = 1 := by
  classical
  rw [← card_matBoxLine n 0]
  have hset : matBoxLine n 0 = {(0 : Matrix (Fin n) (Fin n) ℕ)} := by
    ext M
    rw [matBoxLine, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hbox, -⟩
      rw [mem_matBox] at hbox
      funext i j
      exact Nat.eq_zero_of_le_zero (hbox i j)
    · rintro rfl
      refine ⟨?_, ?_⟩
      · rw [mem_matBox]
        intro i j
        simp
      · exact ⟨fun i => by simp, fun j => by simp⟩
  rw [hset, Finset.card_singleton]


/-! ## Step 2: supports -/

/-- `B` is a **support** when it is the exact support of some semi-magic square of *positive* line
sum.  The empty set is deliberately not a support here: its only square is the zero matrix, of line
sum `0`. -/
def IsSupport (n : ℕ) (B : Finset (Fin n × Fin n)) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ (matFiber n s s B).Nonempty

/-- The supports of `n × n` semi-magic squares, as a finset. -/
noncomputable def supportSet (n : ℕ) : Finset (Finset (Fin n × Fin n)) := by
  classical
  exact (Finset.univ : Finset (Fin n × Fin n)).powerset.filter (IsSupport n)


/-! ## Step 3: one polynomial per support, and one neighbour set per support -/

/-- The polynomial of `isPolyDegLe_gB`, chosen once and for all: its value at `r : ℕ` is the number
of squares of line sum `r + 1` with support exactly `B`. -/
noncomputable def qB (n : ℕ) (B : Finset (Fin n × Fin n)) : Polynomial ℚ :=
  Classical.choose (isPolyDegLe_gB n B)

theorem qB_natDegree (n : ℕ) (B : Finset (Fin n × Fin n)) : (qB n B).natDegree ≤ B.card :=
  (Classical.choose_spec (isPolyDegLe_gB n B)).1

theorem qB_eval (n : ℕ) (B : Finset (Fin n × Fin n)) (r : ℕ) :
    (qB n B).eval (r : ℚ) = gB n B r :=
  (Classical.choose_spec (isPolyDegLe_gB n B)).2 r

/-- **The value attached to a support**: `qB` read one step below line sum `0`.  Rung S5 is the
statement that these numbers sum to `1`. -/
noncomputable def sB (n : ℕ) (B : Finset (Fin n × Fin n)) : ℚ := (qB n B).eval (-1)

theorem sB_eq (n : ℕ) (B : Finset (Fin n × Fin n)) : sB n B = (qB n B).eval (-1) := rfl

/-- The neighbour set of `B`, with the choice of the permutation built in.  If some permutation fits
inside `B`, the split of `SupportSplit.lean` applies and the neighbours are `nbSupp B φ`; otherwise
the fibre is empty at every positive level, so the empty set is the honest coefficient set.  This is
what makes the recurrence below hold at *every* `B`. -/
noncomputable def nbOf (n : ℕ) (B : Finset (Fin n × Fin n)) : Finset (Finset (Fin n × Fin n)) :=
  if h : ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B then
    nbSupp B (matSupport (permMatrix (Classical.choose h)))
  else ∅

/-- **The shifted Spencer recursion, at every support set.**  One level step of the line sum adds
the neighbours and keeps the support. -/
theorem gB_succ (n : ℕ) (B : Finset (Fin n × Fin n)) (r : ℕ) :
    gB n B (r + 1) = gB n B r + ∑ C ∈ nbOf n B, gB n C r := by
  classical
  by_cases h : ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B
  · rw [nbOf, dif_pos h]
    have hstep := card_matFiber_recurrence_succ (n := n) (s := r + 1) (B := B)
      (Classical.choose h) (Classical.choose_spec h)
    change ((matFiber n (r + 1 + 1) (r + 1 + 1) B).card : ℚ)
        = ((matFiber n (r + 1) (r + 1) B).card : ℚ)
          + ∑ C ∈ nbSupp B (matSupport (permMatrix (Classical.choose h))),
              ((matFiber n (r + 1) (r + 1) C).card : ℚ)
    rw [hstep]
    push_cast
    rfl
  · rw [nbOf, dif_neg h, gB_eq_zero_of_no_perm B fun σ hσ => h ⟨σ, hσ⟩]
    simp

/-- **The difference equation.**  The recurrence of `gB_succ`, lifted to the polynomials.  This is
the identity whose value at `X = -1` is the recursion for the numbers `sB`. -/
theorem qB_rec (n : ℕ) (B : Finset (Fin n × Fin n)) :
    (qB n B).comp (X + 1) - qB n B = ∑ C ∈ nbOf n B, qB n C := by
  classical
  rw [← sub_eq_zero]
  refine poly_eq_zero_of_nat_eval_eq_zero fun r => ?_
  have hcast : (r : ℚ) + 1 = ((r + 1 : ℕ) : ℚ) := by push_cast; ring
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_finsetSum, hcast]
  rw [qB_eval n B (r + 1), qB_eval n B r, gB_succ n B r]
  simp_rw [qB_eval]
  ring

/-- **The recursion the numbers `sB` satisfy** — `qB_rec` evaluated at `X = -1`, with no polynomial
left.  The constant is the level-`1` fibre at `B`: it is `1` exactly for the permutation supports,
because a semi-magic square of line sum `1` *is* a permutation matrix. -/
theorem sB_rec (n : ℕ) (B : Finset (Fin n × Fin n)) :
    sB n B = ((matFiber n 1 1 B).card : ℚ) - ∑ C ∈ nbOf n B, sB n C := by
  classical
  have h := congrArg (fun p : Polynomial ℚ => p.eval (-1)) (qB_rec n B)
  have hX : (X + 1 : Polynomial ℚ).eval (-1) = 0 := by simp
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_finsetSum, hX] at h
  -- h : (qB n B).eval 0 - (qB n B).eval (-1) = ∑ C, (qB n C).eval (-1)
  have h0 : (qB n B).eval 0 = ((matFiber n 1 1 B).card : ℚ) := by
    have hc : (0 : ℚ) = ((0 : ℕ) : ℚ) := by norm_num
    rw [hc, qB_eval n B 0]
    show ((matFiber n (0 + 1) (0 + 1) B).card : ℚ) = ((matFiber n 1 1 B).card : ℚ)
    norm_num
  have h' : (qB n B).eval (-1) = ((matFiber n 1 1 B).card : ℚ)
      - ∑ C ∈ nbOf n B, (qB n C).eval (-1) := by
    linarith [h, h0]
  calc sB n B = (qB n B).eval (-1) := sB_eq n B
    _ = ((matFiber n 1 1 B).card : ℚ) - ∑ C ∈ nbOf n B, (qB n C).eval (-1) := h'
    _ = ((matFiber n 1 1 B).card : ℚ) - ∑ C ∈ nbOf n B, sB n C := by
          rw [Finset.sum_congr rfl fun C _ => (sB_eq n C).symm]

/-- Non-supports contribute nothing: if `B` is not the support of any square of positive line sum,
the sequence `gB n B` is zero, so `qB n B = 0` and hence `sB n B = 0`. -/
theorem sB_eq_zero_of_not_isSupport {n : ℕ} {B : Finset (Fin n × Fin n)}
    (h : ¬ IsSupport n B) : sB n B = 0 := by
  classical
  have hzero : qB n B = 0 := by
    refine poly_eq_zero_of_nat_eval_eq_zero fun r => ?_
    have hc : (matFiber n (r + 1) (r + 1) B).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro M hM
      exact h ⟨r + 1, by omega, M, hM⟩
    rw [qB_eval n B r]
    show ((matFiber n (r + 1) (r + 1) B).card : ℚ) = 0
    rw [hc, Nat.cast_zero]
  rw [sB_eq, hzero, Polynomial.eval_zero]


/-! ## Step 4: the single polynomial, read at `t = 0` and at `t ≥ 1` -/

/-- The aggregate: the sum of the support polynomials, shifted down to line sum `t`.  It agrees
with the count `semiMagicCount n t` for every `t ≥ 1`. -/
noncomputable def qAll (n : ℕ) : Polynomial ℚ :=
  (∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, qB n B).comp (X - 1)

theorem qAll_eval_pos {n t : ℕ} (ht : 1 ≤ t) :
    (qAll n).eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  classical
  show ((∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, qB n B).comp (X - 1)).eval (t : ℚ)
    = (semiMagicCount n t : ℚ)
  have hcast : (t : ℚ) - 1 = ((t - 1 : ℕ) : ℚ) := by rw [Nat.cast_sub ht, Nat.cast_one]
  rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_finsetSum, hcast, semiMagicCount_eq_sum_matFiber n t]
  push_cast
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [qB_eval]
  show ((matFiber n (t - 1 + 1) (t - 1 + 1) B).card : ℚ) = ((matFiber n t t B).card : ℚ)
  rw [Nat.sub_add_cancel ht]

/-- **The whole of rung S5 in one evaluation**: the aggregate at line sum `0` is the sum of the
numbers `sB` over the supports.  No information about `t = 0` is available from the recursion, so
this value is unconstrained by `Degree.lean` — it is exactly what S5 asks for. -/
theorem qAll_eval_zero (n : ℕ) :
    (qAll n).eval ((0 : ℕ) : ℚ) = ∑ B ∈ supportSet n, sB n B := by
  classical
  have hsub : supportSet n ⊆ (Finset.univ : Finset (Fin n × Fin n)).powerset := by
    intro B hB
    rw [supportSet, Finset.mem_filter] at hB
    exact hB.1
  show ((∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, qB n B).comp (X - 1)).eval
      ((0 : ℕ) : ℚ) = ∑ B ∈ supportSet n, sB n B
  rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_finsetSum]
  norm_num
  rw [Finset.sum_congr rfl fun B _ => (sB_eq n B).symm]
  exact (Finset.sum_subset hsub fun B hB hBnot =>
    sB_eq_zero_of_not_isSupport fun hs => hBnot (by
      rw [supportSet, Finset.mem_filter]
      exact ⟨hB, hs⟩)).symm


/-! ## Step 5: the two inputs, and what they give -/

/-- **(A)** — Ehrhart–Macdonald reciprocity at `-1`, one support at a time: the value of the
support polynomial at `-1` has the sign `(-1) ^ rankB B`.  Equivalently, the face `F_B` of the
Birkhoff polytope has no interior lattice point at scale `1`.  Mathlib has no Ehrhart theory; this
is the first of the two inputs. -/
def ReciprocityAtNegOne (n : ℕ) : Prop :=
  ∀ B : Finset (Fin n × Fin n), IsSupport n B → sB n B = (-1 : ℚ) ^ rankB B

/-- **(B)** — Euler's formula for the face lattice of the Birkhoff polytope: over the supports the
signs `(-1) ^ dim F` cancel to `1`.  Supports of `B_n` are the non-empty faces of `B_n` and `rankB`
is the face dimension, so this is the polytope-general `Σ_{F} (-1) ^ dim F = 1` and nothing about
Ehrhart.  This is the second input. -/
def FaceLatticeEuler (n : ℕ) : Prop :=
  ∑ B ∈ supportSet n, (-1 : ℚ) ^ rankB B = 1

/-- **(A) and (B) together give rung S5.** -/
theorem sum_sB_eq_one_of (n : ℕ) (hA : ReciprocityAtNegOne n) (hB : FaceLatticeEuler n) :
    ∑ B ∈ supportSet n, sB n B = 1 := by
  classical
  rw [← hB]
  refine Finset.sum_congr rfl fun B hB' => ?_
  exact hA B (by
    rw [supportSet, Finset.mem_filter] at hB'
    exact hB'.2)

/-- **S5, in the form the mission needs it.**  If the numbers `sB` sum to `1` over the supports then
the count `semiMagicCount n` agrees with a polynomial on *all* of `ℕ`, including `t = 0`.

The hypothesis is exactly `Σ_B sB n B = 1`, which `ReciprocityAtNegOne` + `FaceLatticeEuler`
supply — so this is the machine-checked statement that (A) and (B) are the only missing inputs. -/
theorem exists_polynomial_semiMagicCount_of_sum_sB (n : ℕ)
    (h : ∑ B ∈ supportSet n, sB n B = 1) :
    ∃ p : Polynomial ℚ, ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  refine ⟨qAll n, fun t => ?_⟩
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · subst ht0
    rw [qAll_eval_zero, h, semiMagicCount_zero, Nat.cast_one]
  · exact qAll_eval_pos ht1

/-- The same, with the degree bound of `Sharp.lean` kept: if the numbers `sB` sum to `1` then the
polynomial of `exists_polynomial_semiMagicCount_sharp` — which is forced, being the unique degree
`≤ (n-1)^2` polynomial agreeing with the count in infinitely many points — also has the right value
at `t = 0`.  This is the mission's goal, minus the *exactness* of the degree, which is
`exists_polynomial_semiMagicCount_degree_eq` in `Degree.lean`. -/
theorem exists_polynomial_semiMagicCount_degLe_of_sum_sB (n : ℕ)
    (h : ∑ B ∈ supportSet n, sB n B = 1) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ (n - 1) ^ 2 ∧
      ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  classical
  obtain ⟨P, hPdeg, hPval⟩ := exists_polynomial_semiMagicCount_sharp n
  have hagree : ∀ t : ℕ, 1 ≤ t → P.eval (t : ℚ) = (qAll n).eval (t : ℚ) :=
    fun t ht => by rw [hPval t ht, qAll_eval_pos ht]
  have hPeq : P = qAll n := by
    have hsub : P - qAll n = 0 :=
      poly_eq_zero_of_pos_eval_eq_zero fun r hr => by
        rw [Polynomial.eval_sub, hagree r hr, sub_self]
    exact sub_eq_zero.mp hsub
  refine ⟨P, hPdeg, fun t => ?_⟩
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · subst ht0
    rw [hPeq, qAll_eval_zero, h, semiMagicCount_zero, Nat.cast_one]
  · exact hPval t ht1

end MagicSquaresSpencer
