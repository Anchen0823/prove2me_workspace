/-
# Equal sums of two squares, brick 2: an explicit infinite family

Brick 1 supplies the four-parameter identity. This brick records the elementary
one-parameter family

    1^2 + (n^2 - n + 1)^2 = (2n - 1)^2 + (n^2 - n - 1)^2,

which produces **positive solutions with four pairwise distinct entries** for every
`n ≥ 4`, and is injective in `n`, so it yields infinitely many pairwise different
patterns. Every member contains the entry `1`, which makes each member primitive
(gcd of the four entries is `1`) and rules out one member being a nontrivial integer
multiple of another.

## How "positive and pairwise distinct" is formalised

Rather than six separate disequality lemmas, everything is funnelled through the
single strict chain of `explicit_family_chain`:

    1  <  2n - 1  <  n^2 - n - 1  <  n^2 - n + 1   (n ≥ 4).

This one statement simultaneously yields positivity of all four entries
(`explicit_family_pos`) and pairwise distinctness (`explicit_family_ne`), and it is
proved directly by `nlinarith` from `4 ≤ n` with no case split. The bound `4` is sharp:
at `n = 3` the two entries `2n-1 = 5` and `n^2-n-1 = 5` coincide.

Scratch brick, compiled with `lake env lean`; see `missions/two-squares/status.md`.
-/

-- Note (this Mathlib pin): `omega` is provided by the core/tactic environment once the
-- arithmetic tactic bundle below is loaded, and `nlinarith` lives in `Mathlib.Tactic.Linarith`
-- rather than in a module of its own name.
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Int.GCD
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace TwoSquares

/-! ## The identity -/

/-- **Objective 2, equality part.** For every integer `n`,
`1^2 + (n^2 - n + 1)^2 = (2n - 1)^2 + (n^2 - n - 1)^2`.

This is a polynomial identity: it holds for *all* integers `n`, with no positivity
hypothesis. The left entry `1` is written as `1^2` so that the statement literally reads
`a^2 + b^2 = c^2 + d^2` with `a = 1`. -/
theorem explicit_family_identity (n : ℤ) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 := by
  ring

/-! ## The strict chain -/

/-- **Objective 2, inequality part.** For `n ≥ 4` the four entries are strictly ordered as

    1  <  2n - 1  <  n^2 - n - 1  <  n^2 - n + 1.

This is the cleanest single formulation of "positive and pairwise distinct": it implies
both, and unlike a bare list of disequalities it also fixes the size order, which is what
makes later arguments (primitivity, non-scaling) immediate.

The middle inequality is `n^2 - 3n = n(n-3) > 0`; `nlinarith` discharges it unaided
from `4 ≤ n`. The bound `4` is sharp — at `n = 3` we get `2n-1 = 5 = n^2-n-1`. -/
theorem explicit_family_chain {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ) < 2 * n - 1 ∧
      2 * n - 1 < n^2 - n - 1 ∧
        n^2 - n - 1 < n^2 - n + 1 := by
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The four entries are all strictly positive for `n ≥ 4`. -/
theorem explicit_family_pos {n : ℤ} (hn : 4 ≤ n) :
    0 < (1 : ℤ) ∧ 0 < n^2 - n + 1 ∧ 0 < 2 * n - 1 ∧ 0 < n^2 - n - 1 := by
  rcases explicit_family_chain hn with ⟨h1, h2, h3⟩
  constructor
  · norm_num
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The four entries are pairwise distinct for `n ≥ 4`. -/
theorem explicit_family_ne {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ) ≠ 2 * n - 1 ∧
      (1 : ℤ) ≠ n^2 - n - 1 ∧
        (1 : ℤ) ≠ n^2 - n + 1 ∧
          2 * n - 1 ≠ n^2 - n - 1 ∧
            2 * n - 1 ≠ n^2 - n + 1 ∧
              n^2 - n - 1 ≠ n^2 - n + 1 := by
  rcases explicit_family_chain hn with ⟨h1, h2, h3⟩
  have h12 : (1 : ℤ) < n^2 - n - 1 := lt_trans h1 h2
  have h13 : (1 : ℤ) < n^2 - n + 1 := lt_trans h12 h3
  have h23 : 2 * n - 1 < n^2 - n + 1 := lt_trans h2 h3
  exact ⟨ne_of_lt h1, ne_of_lt h12, ne_of_lt h13,
    ne_of_lt h2, ne_of_lt h23, ne_of_lt h3⟩

/-- **Objective 2 assembled.** For every integer `n ≥ 4` the quadruple
`(1, n^2-n+1, 2n-1, n^2-n-1)` is a solution of `a^2 + b^2 = c^2 + d^2` whose four
entries are positive and pairwise distinct — i.e. a genuinely nontrivial solution. -/
theorem explicit_family_solution {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 ∧
      (0 < (1 : ℤ) ∧ 0 < n^2 - n + 1 ∧ 0 < 2 * n - 1 ∧ 0 < n^2 - n - 1) ∧
        ((1 : ℤ) ≠ 2 * n - 1 ∧
          (1 : ℤ) ≠ n^2 - n - 1 ∧
            (1 : ℤ) ≠ n^2 - n + 1 ∧
              2 * n - 1 ≠ n^2 - n - 1 ∧
                2 * n - 1 ≠ n^2 - n + 1 ∧
                  n^2 - n - 1 ≠ n^2 - n + 1) :=
  ⟨explicit_family_identity n, explicit_family_pos hn, explicit_family_ne hn⟩

/-! ## Objective 3: distinct parameters give distinct patterns -/

/-- The family viewed as a single quadruple `(1, n^2-n+1, 2n-1, n^2-n-1)`. -/
def familyQuad (n : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (1, n^2 - n + 1, 2 * n - 1, n^2 - n - 1)

/-- The parametrisation `n ↦ familyQuad n` is injective on all of `ℤ`.

The proof recovers `n` from the linear coordinate `2n - 1`, so no monotonicity argument
(and in particular no hypothesis `n ≥ 4`) is needed. -/
theorem familyQuad_injective : Function.Injective familyQuad := by
  intro m n h
  have hlin : 2 * m - 1 = 2 * n - 1 := by
    simpa [familyQuad] using congrArg (fun t : ℤ × ℤ × ℤ × ℤ => t.2.2.1) h
  omega

/-- **Infinitely many distinct patterns.** The set of quadruples produced by the family
is infinite. Together with `explicit_family_solution` this says the family supplies
infinitely many nontrivial solutions of `a^2 + b^2 = c^2 + d^2`. -/
theorem family_patterns_infinite : (Set.range familyQuad).Infinite :=
  Set.infinite_range_of_injective familyQuad_injective

/-- **Objective 3, inequivalence.** No member of the family is a nontrivial integer
multiple of another: if `familyQuad n = k • familyQuad m` then already `n = m`.

Both members have first entry `1`, so comparing first coordinates forces `k = 1`, and
then injectivity applies. No positivity hypothesis on `k` is needed. -/
theorem family_scaling_trivial {m n k : ℤ} (h : familyQuad n = k • familyQuad m) :
    n = m := by
  have hk : k = 1 := by
    have hcoord := congrArg (fun t : ℤ × ℤ × ℤ × ℤ => t.1) h
    simpa [familyQuad] using hcoord.symm
  subst k
  apply familyQuad_injective
  simpa [familyQuad] using h

/-- Every member of the family is primitive: one entry is `1`, so the gcd of the four
entries is `1`. In particular no member is a nontrivial integer multiple of anything. -/
theorem family_primitive (n : ℤ) :
    Int.gcd (Int.gcd (1 : ℤ) (n^2 - n + 1)) (Int.gcd (2 * n - 1) (n^2 - n - 1)) = 1 := by
  simp [Int.gcd_eq_natAbs]

end TwoSquares
