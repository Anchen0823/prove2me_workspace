# Independent review of the closed-support route

## Conclusion

The mathematical route is sound.  It avoids the old `t = 0` obstruction because it inducts on
counts with **support contained in** a board, rather than counts with support **equal to** a board.
The proof never asserts that an impossible board has a polynomial count at level zero.  Such a
board is used only at levels `t + 1`, where its count is zero.

## Checked points

### The bijection and recurrence

For a permutation support `φ ⊆ B`, subtraction of its permutation matrix bijects

`{T ∈ closedFiber (t+1) B | φ ⊆ support(T)}`

with `closedFiber t B`.  Positivity on every permutation cell makes natural-number subtraction
exact; row and column sums fall by one.  Conversely, adding the permutation matrix raises every
line sum by one, stays inside `B`, and is inverse to subtraction.

The complementary squares miss at least one cell of `φ`.  Inclusion-exclusion over the missing
cells gives

`Σ_{∅ ≠ S ⊆ φ} (-1)^(|S|+1) · closedFiber (t+1) (B \ S)`.

The sign is correct: singleton missing-cell events have positive sign, pair intersections negative,
and so on.  Splitting the fibre into the permutation-positive part and its complement therefore
gives the recurrence used in `ClosedPolynomial.lean`.

Every nonempty `S ⊆ φ ⊆ B` makes `B \ S` a strict subset of `B`.  Thus strong induction on board
cardinality is well founded.  `closedTerms` uses `B ∩ φ`; under `HasPerm n B`, `φ ⊆ B`, so this is
exactly `φ`.

### Impossible boards and level zero

If `B` contains no permutation support, Hall's theorem makes `closedFiber n u B` empty for every
positive `u`.  Its level-zero fibre is nevertheless the singleton zero matrix.  The abstract
recurrence handles this correctly: a bad child is sampled only at `t + 1`, and is represented there
by the zero polynomial.  No claim is made about its value at zero.

For a good board, discrete antiderivation starts with the actual constant `b B 0`.  Hence the
constructed polynomial agrees at zero by construction, while its forward difference is determined
by child counts at positive levels.  In fact every closed fibre at level zero contains exactly the
zero matrix, but the proof does not need a separate global lemma stating this.

### Orders zero and one

For `n = 0`, the empty permutation has empty support, so the full empty board satisfies `HasPerm`.
The inclusion-exclusion term set is empty and the recurrence says the count is constant.  This
matches the unique empty matrix, whose vacuous row and column conditions hold at every line sum.
The exact-degree theorem is only invoked under `1 ≤ n`, so truncated subtraction in `(n-1)^2`
causes no issue.

For `n = 1`, the full board has one permutation cell.  Its only child after deleting that cell has
no supported permutation and has zero count at positive levels.  The recurrence again yields the
constant polynomial `1`, of degree `(1-1)^2 = 0`.

## Why this does not contradict `S5-NOTES.md`

The earlier obstruction concerns the exact-support functions
`h_B(t) = #{T | support(T) = B}`.  The empty exact support has the delta sequence
`h_∅(0) = 1` and `h_∅(t) = 0` for `t > 0`; it is not polynomial.  It occurs in the exact-support
split at the zero-to-one boundary, so the positive-level recursion loses the initial value needed
to determine the aggregate polynomial at zero.  That analysis remains correct.

The new route changes the functions being inducted on.  A closed-support count includes the zero
matrix at level zero for every board.  More significantly, its recurrence writes the forward
difference of a good board using smaller boards evaluated at the **new positive level** `t + 1`.
Impossible smaller boards therefore contribute zero, even though their isolated level-zero value
is non-polynomial.  The good board's own zero value is supplied as the integration constant.  The
proof then applies directly to the full board, whose closed fibre is the whole semi-magic-square
set.  It never decomposes the zero matrix into exact supports and never extrapolates a positive-only
polynomial backward to zero.

Thus the route is an elementary finite-difference/inclusion-exclusion proof of the needed
all-nonnegative polynomiality.  It does not prove Ehrhart reciprocity, and it does not make each
exact-support count polynomial at zero.

## Verification status

Mathematically verified in this review:

- add/subtract permutation bijection and its hypotheses;
- inclusion-exclusion event, sign, and deleted-board interpretation;
- strict decrease required for strong induction;
- treatment of impossible boards only at positive levels;
- discrete-antiderivative initial value at level zero;
- edge cases `n = 0` and `n = 1`;
- identification of the full-board closed fibre with `semiMagicCount`.

Mechanically verified before this review:

- `S5Bridge.lean` compiles with the pinned Lean 4.33.1 toolchain;
- `ClosedSupport.lean` compiles with the pinned Lean 4.33.1 toolchain.

Pending at the time of this review:

- a clean compile of `ClosedSupportIE.lean`, `PolynomialRecurrence.lean`, and
  `ClosedPolynomial.lean` together after integration;
- the project library/root build and final axiom audit.
