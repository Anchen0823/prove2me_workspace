# Read-back: `family_patterns_infinite`

Declared in namespace `EqualTwoSquares` (file `items/family_patterns_infinite.lean`); the name agrees with the file name. Its own doc line reads *"Objective 3: the family produces infinitely many distinct quadruples."*

## What the declaration literally says

Let

$$F : \mathbb{Z} \longrightarrow \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}, \qquad F(n) = \bigl(1,\; n^2 - n + 1,\; 2n - 1,\; n^2 - n - 1\bigr),$$

and let $S = \{\,F(n) : n \in \mathbb{Z}\,\}$ be its set-theoretic image (the range of $F$, taken as a set of four-tuples of integers). Then $S$ is **infinite** — i.e. $S$ is not finite; equivalently there is no finite list exhausting all quadruples produced by the family, and in particular the family does not collapse to finitely many values (it does not, for instance, become eventually constant or periodic-with-finite-image).

There are no hypotheses and no free variables other than the set $S$ itself, which is defined inside the statement. The quantification is over all integers $n$, including negative ones, so the range includes the values coming from negative indices as well; nothing restricts $n$ to be large, positive, or pairwise distinct.

Infinitude here is witnessed by injectivity: distinct indices give distinct tuples (already the coordinate $2n-1$ separates them), so the range of $F$ is in bijection with the infinite set $\mathbb{Z}$.

## Audit notes

- **Truth.** Verified: no repetition among $F(n)$ for all $|n| \le 2000$, and the general argument is that coordinate 3, $2n-1$, is injective in $n$, so the range is infinite. **TRUE.**
- **Faithfulness.** Name matches file name; the doc line's "infinitely many distinct quadruples" corresponds precisely to infinitude of the range set. Every variable is bound (the bound index $n$ lives inside the set comprehension); nothing free.
- **Trivializing premise.** None: the declaration is a closed formula with no hypotheses.
- **Satisfiability.** Nothing to satisfy; the statement is a property of a concretely defined non-empty set and is non-vacuous.
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
