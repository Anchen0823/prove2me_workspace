import Mathlib

set_option autoImplicit false

open scoped BigOperators

/-!
# Compositions of an integer into a fixed number of parts

A **composition of `n` into `k` parts** is a $k$-tuple of nonnegative integers
summing to $n$. The classical *stars and bars* count is

$$\#\\{x\in\mathbb{N}^{k} : x_{1}+\cdots+x_{k}=n\\}=\binom{n+k-1}{n}.$$

Because $\mathbb{N}^{k}$ is infinite, the count is taken inside a box: for a
bound `N` we consider `comps N k n`, the set of functions `Fin k → Fin (N+1)`
whose values sum to `n`. When `n ≤ N` this is lossless — every coordinate of
such a tuple is at most `n`, hence at most `N` — so the box does not change the
count. Holding `N` fixed while `k` and `n` vary is also what makes the
induction work: splitting off the first coordinate produces a tail that still
lives in the same box.

The evaluation `(comps N k n).card = (n + k - 1).choose n` is submitted
separately as a theorem; it is the form of stars and bars needed to count
MacMahon's parametrization of $3\times3$ semi-magic squares.
-/

namespace MagicSquares

/-- The compositions of `n` into `k` parts, with every part bounded by `N`.
For `n ≤ N` the bound is inactive. -/
def comps (N k n : ℕ) : Finset (Fin k → Fin (N + 1)) :=
  by
    classical
    exact Finset.univ.filter fun q => (∑ i : Fin k, (q i : ℕ)) = n

/-- The number of compositions of `n` into `k` parts. -/
def compsCount (N k n : ℕ) : ℕ := (comps N k n).card

end MagicSquares
