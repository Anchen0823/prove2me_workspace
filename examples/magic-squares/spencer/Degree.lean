/-
# Brick 11: the exact degree — the matching lower bound

`Sharp.lean` gives the upper bound `natDegree ≤ (n-1)^2` on the polynomial that counts semi-magic
squares of line sum `t ≥ 1`.  This brick supplies the matching **lower** bound, by exhibiting an
explicit family with `(n-1)^2` free parameters.

For a square of order `n + 1` and a line sum `(n + 1) * s`, take any

  `c : Fin n → Fin n → Fin (s / n + 1)`

and build the `(n + 1) × (n + 1)` matrix

* `M p q = s + c p q` on the top-left `n × n` block,
* `M p last = s - Σ_q c p q` in the last column,
* `M last q = s - Σ_p c p q` in the last row,
* `M last last = s + Σ_{p,q} c p q` at the corner.

Each line sums to `n * s + Σ c + (s - Σ c) = (n + 1) * s`, and the bound `c p q ≤ s / n` guarantees
`Σ_q c p q ≤ n * (s / n) ≤ s`, so every entry is a natural number.  The block is recovered from `M`
by `c p q = M p q - s`, so the family is injective and has `(s / n + 1) ^ (n * n)` elements:

  `semiMagicCount (n + 1) ((n + 1) * s) ≥ (s / n + 1) ^ (n * n)`.

That is a lower bound growing like `s ^ ((n+1) - 1) ^ 2`, so the counting polynomial (which agrees
with `semiMagicCount` for `t ≥ 1`) cannot have smaller degree.  Combined with `Sharp.lean` this
gives the **exact** degree `(n - 1) ^ 2` for `t ≥ 1`
(`exists_polynomial_semiMagicCount_degree_eq`).

Agreement at `t = 0` is *not* claimed here — that is the reciprocity statement (rung S5), and it is
the reason the platform's `semi_magic_polynomial_exists` is still open.  The theorems in this file
are **new** declarations; nothing published is edited.
-/

import Mathlib
import Definitions.Def_MagicSquares
import examples.«magic-squares».spencer.Sharp

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares

/-! ## 1. The explicit family -/

/-- The block index of an index of `Fin (n+1)`: the identity on the first `n` indices, and the junk
value `0` on the last one.  The junk value is never used: `blockIdx` is only ever evaluated in
branches whose index is known to be one of the first `n`. -/
def blockIdx {n : ℕ} (hn : 1 ≤ n) (j : Fin (n + 1)) : Fin n :=
  ⟨min (j : ℕ) (n - 1), by have := j.isLt; omega⟩

theorem blockIdx_castSucc {n : ℕ} (hn : 1 ≤ n) (j : Fin n) :
    blockIdx hn (Fin.castSucc j) = j := by
  refine Fin.ext ?_
  show min ((Fin.castSucc j : Fin (n + 1)) : ℕ) (n - 1) = (j : ℕ)
  rw [Fin.val_castSucc, Nat.min_eq_left (by have := j.isLt; omega)]

/-- **The linear family.**  The free block `c` on the first `n` rows/columns, and the last row and
column filled in by the line-sum conditions: every line sums to `(n + 1) * s`. -/
def lowerBlock (n s : ℕ) (hn : 1 ≤ n) (c : Fin n → Fin n → Fin (s / n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℕ :=
  fun i j =>
    if (i : ℕ) = n then
      (if (j : ℕ) = n then s + ∑ p : Fin n, ∑ q : Fin n, (c p q : ℕ)
       else s - ∑ p : Fin n, (c p (blockIdx hn j) : ℕ))
    else
      (if (j : ℕ) = n then s - ∑ q : Fin n, (c (blockIdx hn i) q : ℕ)
       else s + (c (blockIdx hn i) (blockIdx hn j) : ℕ))

/-- The block entries of the family. -/
theorem lowerBlock_castSucc_castSucc {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) (p q : Fin n) :
    lowerBlock n s hn c (Fin.castSucc p) (Fin.castSucc q) = s + (c p q : ℕ) := by
  have hi : ¬(((Fin.castSucc p : Fin (n + 1)) : ℕ) = n) := by
    rw [Fin.val_castSucc]; exact ne_of_lt p.isLt
  have hj : ¬(((Fin.castSucc q : Fin (n + 1)) : ℕ) = n) := by
    rw [Fin.val_castSucc]; exact ne_of_lt q.isLt
  simp only [lowerBlock]
  rw [if_neg hi, if_neg hj, blockIdx_castSucc hn p, blockIdx_castSucc hn q]

/-- The last column of the family. -/
theorem lowerBlock_castSucc_last {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) (p : Fin n) :
    lowerBlock n s hn c (Fin.castSucc p) (Fin.last n) = s - ∑ q : Fin n, (c p q : ℕ) := by
  have hi : ¬(((Fin.castSucc p : Fin (n + 1)) : ℕ) = n) := by
    rw [Fin.val_castSucc]; exact ne_of_lt p.isLt
  simp only [lowerBlock]
  rw [if_neg hi, if_pos (Fin.val_last n), blockIdx_castSucc hn p]

/-- The last row of the family. -/
theorem lowerBlock_last_castSucc {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) (q : Fin n) :
    lowerBlock n s hn c (Fin.last n) (Fin.castSucc q) = s - ∑ p : Fin n, (c p q : ℕ) := by
  have hj : ¬(((Fin.castSucc q : Fin (n + 1)) : ℕ) = n) := by
    rw [Fin.val_castSucc]; exact ne_of_lt q.isLt
  simp only [lowerBlock]
  rw [if_pos (Fin.val_last n), if_neg hj, blockIdx_castSucc hn q]

/-- The corner of the family. -/
theorem lowerBlock_last_last {n s : ℕ} (hn : 1 ≤ n) (c : Fin n → Fin n → Fin (s / n + 1)) :
    lowerBlock n s hn c (Fin.last n) (Fin.last n)
      = s + ∑ p : Fin n, ∑ q : Fin n, (c p q : ℕ) := by
  simp only [lowerBlock]
  rw [if_pos (Fin.val_last n), if_pos (Fin.val_last n)]

/-! ## 2. Natural subtraction, and the size of a block line -/

/-- Natural subtraction does not distribute over a sum, so this needs the pointwise bound. -/
theorem sum_sub_const {α : Type*} (u : Finset α) (X : α → ℕ) (a : ℕ) (h : ∀ i ∈ u, X i ≤ a) :
    ∑ i ∈ u, (a - X i) = u.card * a - ∑ i ∈ u, X i := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert x u hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, Finset.card_insert_of_notMem hx]
      have hx' : X x ≤ a := h x (Finset.mem_insert_self x u)
      have hb : ∑ i ∈ u, X i ≤ u.card * a :=
        calc ∑ i ∈ u, X i ≤ ∑ _i ∈ u, a :=
              Finset.sum_le_sum fun i hi => h i (Finset.mem_insert_of_mem hi)
          _ = u.card * a := by simp
      rw [ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
      have h1 : (a - X x) + (u.card * a - ∑ i ∈ u, X i)
          = (u.card * a + a) - (X x + ∑ i ∈ u, X i) := by omega
      have h2 : u.card * a + a = (u.card + 1) * a := by ring
      rw [h1, h2]

/-- The `univ` form of `sum_sub_const`. -/
theorem sum_univ_sub_const {n : ℕ} (X : Fin n → ℕ) (a : ℕ) (h : ∀ i, X i ≤ a) :
    ∑ i : Fin n, (a - X i) = n * a - ∑ i : Fin n, X i := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    sum_sub_const (Finset.univ : Finset (Fin n)) X a fun i _ => h i

/-- A row of the block sums to at most `n * (s / n) ≤ s`. -/
theorem sum_lowerC_le {n s : ℕ} (c : Fin n → Fin n → Fin (s / n + 1)) (p : Fin n) :
    ∑ q : Fin n, (c p q : ℕ) ≤ s := by
  calc ∑ q : Fin n, (c p q : ℕ) ≤ ∑ _q : Fin n, s / n :=
        Finset.sum_le_sum fun q _ => by have := (c p q).isLt; omega
    _ = n * (s / n) := by simp
    _ ≤ s := Nat.mul_div_le s n

/-- A column of the block sums to at most `n * (s / n) ≤ s`. -/
theorem sum_lowerC_le_col {n s : ℕ} (c : Fin n → Fin n → Fin (s / n + 1)) (q : Fin n) :
    ∑ p : Fin n, (c p q : ℕ) ≤ s := by
  calc ∑ p : Fin n, (c p q : ℕ) ≤ ∑ _p : Fin n, s / n :=
        Finset.sum_le_sum fun p _ => by have := (c p q).isLt; omega
    _ = n * (s / n) := by simp
    _ ≤ s := Nat.mul_div_le s n

/-! ## 3. All four kinds of line sum to `(n + 1) * s` -/

/-- The "block line" pattern: `(Σ (s + Y i)) + (s - Σ Y i) = (n + 1) * s`. -/
theorem sum_add_sub_sum {n s : ℕ} (Y : Fin n → ℕ) (h : ∑ i : Fin n, Y i ≤ s) :
    (∑ i : Fin n, (s + Y i)) + (s - ∑ i : Fin n, Y i) = (n + 1) * s := by
  rw [Finset.sum_add_distrib, Finset.sum_const_nat fun i _ => rfl, Finset.card_univ,
    Fintype.card_fin, Nat.add_assoc, Nat.add_sub_of_le h]
  ring

/-- The "last line" pattern: `(Σ (s - Y i)) + (s + Σ Y i) = (n + 1) * s`. -/
theorem sum_sub_add_sum {n s : ℕ} (Y : Fin n → ℕ) (h : ∀ i, Y i ≤ s)
    (hT : ∑ i : Fin n, Y i ≤ n * s) :
    (∑ i : Fin n, (s - Y i)) + (s + ∑ i : Fin n, Y i) = (n + 1) * s := by
  rw [sum_univ_sub_const Y s h, Nat.add_comm s (∑ i : Fin n, Y i), ← Nat.add_assoc,
    Nat.sub_add_cancel hT]
  ring

theorem lowerBlock_rowSum_castSucc {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) (p : Fin n) :
    ∑ j : Fin (n + 1), lowerBlock n s hn c (Fin.castSucc p) j = (n + 1) * s := by
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_congr rfl fun q _ => lowerBlock_castSucc_castSucc hn c p q,
    lowerBlock_castSucc_last hn c p]
  exact sum_add_sub_sum (fun q : Fin n => (c p q : ℕ)) (sum_lowerC_le c p)

theorem lowerBlock_colSum_castSucc {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) (q : Fin n) :
    ∑ i : Fin (n + 1), lowerBlock n s hn c i (Fin.castSucc q) = (n + 1) * s := by
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_congr rfl fun p _ => lowerBlock_castSucc_castSucc hn c p q,
    lowerBlock_last_castSucc hn c q]
  exact sum_add_sub_sum (fun p : Fin n => (c p q : ℕ)) (sum_lowerC_le_col c q)

/-- The total of the block. -/
theorem sum_lowerC_total_le {n s : ℕ} (c : Fin n → Fin n → Fin (s / n + 1)) :
    ∑ p : Fin n, ∑ q : Fin n, (c p q : ℕ) ≤ n * s :=
  calc ∑ p : Fin n, ∑ q : Fin n, (c p q : ℕ) ≤ ∑ _p : Fin n, s :=
        Finset.sum_le_sum fun p _ => sum_lowerC_le c p
    _ = n * s := by simp

theorem lowerBlock_rowSum_last {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) :
    ∑ j : Fin (n + 1), lowerBlock n s hn c (Fin.last n) j = (n + 1) * s := by
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_congr rfl fun q _ => lowerBlock_last_castSucc hn c q, lowerBlock_last_last hn c]
  rw [← Finset.sum_comm]
  refine sum_sub_add_sum (fun q : Fin n => ∑ p : Fin n, (c p q : ℕ))
    (fun q => sum_lowerC_le_col c q) ?_
  rw [Finset.sum_comm]
  exact sum_lowerC_total_le c

theorem lowerBlock_colSum_last {n s : ℕ} (hn : 1 ≤ n)
    (c : Fin n → Fin n → Fin (s / n + 1)) :
    ∑ i : Fin (n + 1), lowerBlock n s hn c i (Fin.last n) = (n + 1) * s := by
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_congr rfl fun p _ => lowerBlock_castSucc_last hn c p, lowerBlock_last_last hn c]
  exact sum_sub_add_sum (fun p : Fin n => ∑ q : Fin n, (c p q : ℕ))
    (fun p => sum_lowerC_le c p) (sum_lowerC_total_le c)

/-- **Every line of the family sums to the same value.** -/
theorem lowerBlock_lineSums {n s : ℕ} (hn : 1 ≤ n) (c : Fin n → Fin n → Fin (s / n + 1)) :
    LineSums (lowerBlock n s hn c) ((n + 1) * s) :=
  ⟨fun i => Fin.lastCases (motive := fun i =>
        ∑ j : Fin (n + 1), lowerBlock n s hn c i j = (n + 1) * s)
      (lowerBlock_rowSum_last hn c) (fun p => lowerBlock_rowSum_castSucc hn c p) i,
   fun j => Fin.lastCases (motive := fun j =>
        ∑ i : Fin (n + 1), lowerBlock n s hn c i j = (n + 1) * s)
      (lowerBlock_colSum_last hn c) (fun q => lowerBlock_colSum_castSucc hn c q) j⟩

/-- The family lies in the box of line sum `(n + 1) * s`. -/
theorem lowerBlock_mem {n s : ℕ} (hn : 1 ≤ n) (c : Fin n → Fin n → Fin (s / n + 1)) :
    lowerBlock n s hn c ∈ matBoxLine (n + 1) ((n + 1) * s) := by
  classical
  have hls := lowerBlock_lineSums hn c
  rw [matBoxLine, Finset.mem_filter, mem_matBox]
  exact ⟨fun i j => le_of_rowSum hls.1 i j, hls⟩

/-- **The family is injective**: the block is recovered from the matrix by `c p q = M p q - s`. -/
theorem lowerBlock_injective {n s : ℕ} (hn : 1 ≤ n) :
    Function.Injective (lowerBlock (n := n) (s := s) hn) := by
  intro c c' h
  funext p q
  have hpq := congrFun (congrFun h (Fin.castSucc p)) (Fin.castSucc q)
  rw [lowerBlock_castSucc_castSucc hn c p q, lowerBlock_castSucc_castSucc hn c' p q] at hpq
  exact Fin.ext (Nat.add_left_cancel hpq)

/-! ## 4. The counting lower bound -/

/-- **The explicit lower bound for the semi-magic count.**  For squares of order `n + 1` and line
sum `(n + 1) * s` there are at least `(s / n + 1) ^ (n * n)` of them. -/
theorem semiMagicCount_ge_family (n s : ℕ) (hn : 1 ≤ n) :
    (s / n + 1) ^ (n * n) ≤ semiMagicCount (n + 1) ((n + 1) * s) := by
  classical
  have hcard : (Finset.univ.image (lowerBlock (n := n) (s := s) hn)).card
      = (s / n + 1) ^ (n * n) := by
    rw [Finset.card_image_of_injective _ (lowerBlock_injective hn), Finset.card_univ,
      Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rw [← hcard, ← card_matBoxLine (n + 1) ((n + 1) * s)]
  refine Finset.card_le_card fun M hM => ?_
  rw [Finset.mem_image] at hM
  obtain ⟨c, -, rfl⟩ := hM
  exact lowerBlock_mem hn c

/-! ## 5. A polynomial growing faster than `x ^ d` has degree at least `d` -/

/-- A polynomial evaluated at `x ≥ 1` is bounded by a constant times `x ^ natDegree`. -/
theorem eval_le_mul_pow {p : Polynomial ℚ} {x : ℚ} (hx : 1 ≤ x) :
    p.eval x ≤ (∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|) * x ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k ≤ p.natDegree := by
    have := Finset.mem_range.mp hk
    omega
  have hx0 : (0 : ℚ) ≤ x := le_trans zero_le_one hx
  calc p.coeff k * x ^ k ≤ |p.coeff k| * x ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hx0 k)
    _ ≤ |p.coeff k| * x ^ p.natDegree :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hk') (abs_nonneg _)

/-- **Growth forces the degree.**  If a rational polynomial dominates `x ^ d` at the integer
argument `A * s` for every `s ≥ 1`, where `1 ≤ A`, then its degree is at least `d`.

The proof is the elementary one: `p.eval x ≤ B * x ^ e` for `x ≥ 1` (`B` = sum of the absolute
values of the coefficients, `e = p.natDegree`), while at a large `s` the hypothesis together with
`s ^ d = s ^ (d - e) * s ^ e` and `s ^ (d - e) ≥ s` forces `s ≤ B * A ^ e < s` when `e < d`. -/
theorem le_natDegree_of_lowerBound {p : Polynomial ℚ} {d : ℕ} {A : ℚ} (hA : 1 ≤ A)
    (h : ∀ s : ℕ, 1 ≤ s → (s : ℚ) ^ d ≤ p.eval (A * (s : ℚ))) : d ≤ p.natDegree := by
  by_contra hcon
  push Not at hcon
  set e : ℕ := p.natDegree with he
  set B : ℚ := ∑ k ∈ Finset.range (e + 1), |p.coeff k| with hB
  obtain ⟨s, hs1, hlarge⟩ : ∃ s : ℕ, 1 ≤ s ∧ B * A ^ e < (s : ℚ) := by
    obtain ⟨t, ht⟩ := exists_nat_gt (B * A ^ e)
    refine ⟨max t 1, le_max_right _ _, ?_⟩
    exact lt_of_lt_of_le ht (by exact_mod_cast le_max_left t 1)
  have hs1' : (1 : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs1
  have hse : (0 : ℚ) < (s : ℚ) ^ e := pow_pos (by linarith) e
  have hub : p.eval (A * (s : ℚ)) ≤ B * A ^ e * (s : ℚ) ^ e := by
    calc p.eval (A * (s : ℚ))
        ≤ B * (A * (s : ℚ)) ^ e := by
          rw [he, hB]
          exact eval_le_mul_pow (by nlinarith [hA, hs1'])
      _ = B * A ^ e * (s : ℚ) ^ e := by rw [mul_pow]; ring
  have hlow : (s : ℚ) ^ d ≤ p.eval (A * (s : ℚ)) := h s hs1
  have hpow : (s : ℚ) ^ d = (s : ℚ) ^ (d - e) * (s : ℚ) ^ e := by
    rw [← pow_add, Nat.sub_add_cancel (le_of_lt hcon)]
  have hge : (s : ℚ) ≤ (s : ℚ) ^ (d - e) := by
    calc (s : ℚ) = (s : ℚ) ^ 1 := (pow_one _).symm
      _ ≤ (s : ℚ) ^ (d - e) := pow_le_pow_right₀ hs1' (by omega)
  have hsme : (s : ℚ) * (s : ℚ) ^ e ≤ B * A ^ e * (s : ℚ) ^ e := by
    calc (s : ℚ) * (s : ℚ) ^ e ≤ (s : ℚ) ^ (d - e) * (s : ℚ) ^ e :=
          mul_le_mul_of_nonneg_right hge (le_of_lt hse)
      _ = (s : ℚ) ^ d := hpow.symm
      _ ≤ p.eval (A * (s : ℚ)) := hlow
      _ ≤ B * A ^ e * (s : ℚ) ^ e := hub
  have hcancel : (s : ℚ) ≤ B * A ^ e := le_of_mul_le_mul_right hsme hse
  linarith

/-! ## 6. The exact degree for `t ≥ 1` -/

/-- **Spencer's theorem with the exact degree.**  For `n ≥ 1` there is one polynomial of degree
exactly `(n - 1) ^ 2` that counts the `n × n` semi-magic squares of line sum `t` for every `t ≥ 1`.

Upper bound: `Sharp.lean`.  Lower bound: the explicit family of `§1`–`§4`, via the growth lemma
above.  This is a **new** declaration; `exists_polynomial_semiMagicCount_pos` and
`exists_polynomial_semiMagicCount_sharp` are untouched.  Agreement at `t = 0` is *not* claimed —
that is the reciprocity statement (rung S5). -/
theorem exists_polynomial_semiMagicCount_degree_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  obtain ⟨p, hpdeg, hpval⟩ := exists_polynomial_semiMagicCount_sharp n
  by_cases hn2 : 1 < n
  · have hnn : 1 ≤ n - 1 := by omega
    have hbound : ∀ u : ℕ, 1 ≤ u →
        (u : ℚ) ^ ((n - 1) * (n - 1)) ≤ p.eval (((n - 1) * n : ℕ) * (u : ℚ)) := by
      intro u hu
      have hfam := semiMagicCount_ge_family (n - 1) ((n - 1) * u) hnn
      rw [Nat.mul_div_cancel_left u (by omega), Nat.sub_add_cancel hn] at hfam
      have hval := hpval (n * ((n - 1) * u))
        (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
      have hkey : ((u : ℚ) + 1) ^ ((n - 1) * (n - 1))
          ≤ p.eval ((n * ((n - 1) * u) : ℕ) : ℚ) := by
        have hcast : ((u : ℚ) + 1) ^ ((n - 1) * (n - 1))
            = (((u + 1) ^ ((n - 1) * (n - 1)) : ℕ) : ℚ) := by
          push_cast
          ring
        rw [hval, hcast]
        exact Nat.cast_le.mpr hfam
      calc (u : ℚ) ^ ((n - 1) * (n - 1))
          ≤ ((u : ℚ) + 1) ^ ((n - 1) * (n - 1)) := by
            refine pow_le_pow_left₀ (by positivity) ?_ _
            have : (1 : ℚ) ≤ (u : ℚ) := by exact_mod_cast hu
            linarith
        _ ≤ p.eval ((n * ((n - 1) * u) : ℕ) : ℚ) := hkey
        _ = p.eval (((n - 1) * n : ℕ) * (u : ℚ)) := by
            congr 1
            push_cast
            ring
    have hge : (n - 1) * (n - 1) ≤ p.natDegree :=
      le_natDegree_of_lowerBound (A := (((n - 1) * n : ℕ) : ℚ)) (by
        have h2 : (1 : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by
          exact_mod_cast (show 1 ≤ n - 1 by omega)
        have h3 : (1 : ℚ) ≤ ((n : ℕ) : ℚ) := by
          exact_mod_cast (show 1 ≤ n by omega)
        push_cast
        nlinarith) hbound
    refine ⟨p, le_antisymm hpdeg ?_, hpval⟩
    rw [pow_two]
    exact hge
  · -- `n ≤ 1`: then `(n - 1) ^ 2 = 0`, so there is no lower bound to prove
    have hn1 : n ≤ 1 := by omega
    have h0 : (n - 1) ^ 2 = 0 := by
      have : n - 1 = 0 := by omega
      rw [this]; norm_num
    refine ⟨p, ?_, hpval⟩
    rw [h0] at hpdeg ⊢
    exact le_antisymm hpdeg (Nat.zero_le _)

end MagicSquaresSpencer
