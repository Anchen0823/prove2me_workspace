# Reuse search: Eulerian, Weisner, and polytope-face infrastructure

Read-only Prove2Me queries on 2026-09-22 used the pinned environment parameter
`env=0df444a360eaa60ab8c11dca51a86af692955474`.

| Query | Result | Reuse assessment |
| --- | --- | --- |
| `q=Weisner` | 0 results (already checked before this refresh) | No submitted Weisner theorem to reuse. |
| `q=Eulerian` | 15 results | All returned results were unrelated uses of the word “Eulerian” (Euler tours, Eulerian PDE language, and similar); none stated an Eulerian-poset or Möbius-interval result. |
| `q=face lattice` | 0 results | No face-lattice theorem available. |
| `q=Euler polytope` | 0 results | No polytope Euler relation available. |

Conclusion: the current pinned platform offers no reusable theorem that fills the
finite matching-boundary gap.  In particular, it does not supply the required
face/support dictionary, Eulerian Möbius formula for Birkhoff-face intervals,
or dual Weisner cancellation.  The remaining `phi not_subset D` zero-sum branch
therefore needs a new finite child theorem or local formalization; the proven
`phi subseteq D` branch does not reduce that gap.

No platform write or publication was performed.
