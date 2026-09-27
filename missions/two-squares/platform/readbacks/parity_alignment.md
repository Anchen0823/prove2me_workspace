# Read-back: `parity_alignment`

Declared in namespace `EqualTwoSquares` (file `items/parity_alignment.lean`); the name agrees with the file name. Its own doc line reads *"Objective 4, parity: after possibly swapping c and d, matching entries have equal parity."*

## What the declaration literally says

Let $a, b, c, d \in \mathbb{Z}$ satisfy the single hypothesis

$$a^2 + b^2 \;=\; c^2 + d^2 .$$

Then at least one of the following two alternatives holds:

1. $a - c$ is even **and** $b - d$ is even; or
2. $a - d$ is even **and** $b - c$ is even.

Here "even" means divisible by $2$ *inside $\mathbb{Z}$*, i.e. the difference is $2k$ for some integer $k$; this is symmetric in sign, so it is the same as saying that the two entries have the same parity. The disjunction is inclusive. Note carefully which pairings occur: the first branch pairs $a$ with $c$ and $b$ with $d$ (the pairing given by the *order of the two sides of the equation* $(a,b) \mid (c,d)$), and the second branch pairs $a$ with $d$ and $b$ with $c$ (the pairing obtained after swapping the roles of $c$ and $d$), matching the doc line. Nothing is assumed about the entries: they may be zero, negative, or coincide, and no coprimality or non-degeneracy is required.

Cases covered silently: $a=b=c=d=0$; all entries odd; all entries even; and mixed cases where exactly one entry on each side is odd — including the genuinely mixed sub-case $a, b, c, d \equiv 1, 0, 0, 1 \pmod 2$ (e.g. $a=1, b=8, c=4, d=7$: $1^2+8^2 = 65 = 4^2+7^2$), where the first alternative fails ($a-c = -3$ and $b-d = 1$ are odd) and the conclusion survives only through the second alternative ($a-d = -6$ and $b-c = 4$ are even). So neither disjunct alone is implied by the hypothesis, and the disjunction is genuinely needed.

## Audit notes

- **Truth.** TRUE. Proof of the (mod $4$) content: a square is $\equiv 0 \pmod 4$ when its base is even and $\equiv 1 \pmod 4$ when odd; hence, writing $A$ for the number of odd entries among $\{a,b\}$ and $C$ for the number of odd entries among $\{c,d\}$, the hypothesis gives $A \equiv C \pmod 4$. Since $A, C \in \{0,1,2\}$, this forces $A = C$. If $A = C \in \{0,2\}$ then $a,b,c,d$ are all even or all odd, so $a - c$ and $b - d$ are even (branch 1). If $A = C = 1$: when the odd entry on the left and the odd entry on the right occupy corresponding positions ($a$ odd and $c$ odd, or $b$ odd and $d$ odd) branch 1 again gives even differences; when they occupy crossed positions ($a$ odd, $d$ odd, $b,c$ even, or $b$ odd, $c$ odd, $a,d$ even) then $a-d$ and $b-c$ are even, i.e. branch 2. Note that the naive mod-$2$ argument would be insufficient (it only gives that $a-c$ and $b-d$ have equal parity); the count of odd entries, obtained from the stronger mod-$4$ information, is what makes the statement true — and, indeed, the case analysis above shows no counterexample can hide in the "both differences odd" corner, because then the cross differences are automatically even. Exhaustive verification: all quadruples with $a,b,c,d \in [-24,24]$ satisfying the hypothesis (checked side by side with the conclusion) produce zero failures. An additional random/high-value search for entries beyond that box likewise produced none. **No counterexample.**
- **Faithfulness.** Name matches file name. The doc line "after possibly swapping $c$ and $d$, matching entries have equal parity" corresponds exactly to the two-branch structure with the two pairings $(a,c),(b,d)$ and $(a,d),(b,c)$. All four variables are implicit arguments bound by the statement, all appear in the hypothesis, and all appear in the conclusion; nothing is free.
- **Trivializing premise.** None: $a^2+b^2 = c^2+d^2$ is the object of study, not a restatement of the parity conclusion, and it is neither contradictory nor strong enough to make the conclusion vacuous. Interesting instances are plentiful (see $(1,8,4,7)$ above, where only one branch survives).
- **Satisfiability.** Satisfiable, non-vacuously and with rich instances: $(0,0,0,0)$, $(3,4,5,0)$, $(1,8,4,7)$, and every member of the explicit family $(1, n^2-n+1, 2n-1, n^2-n-1)$. Infinitely many witnesses.
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
