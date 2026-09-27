# Read-back: `complete_parametrization`

Declared in namespace `EqualTwoSquares` (file `items/complete_parametrization.lean`); the name agrees with the file name. Its own doc line reads *"Objective 6, the goal: the four-parameter parametrisation is complete."*

## What the declaration literally says

Let $a, b, c, d \in \mathbb{Z}$ satisfy the single hypothesis

$$a^2 + b^2 \;=\; c^2 + d^2 .$$

Then **at least one** of the following two alternatives holds:

- **Branch 1:** there exist integers $p, q, r, s$ with

  $$a = p r + q s, \qquad b = p s - q r, \qquad c = p r - q s, \qquad d = p s + q r ;$$

- **Branch 2:** there exist integers $p, q, r, s$ with

  $$a = p r + q s, \qquad b = p s - q r, \qquad d = p r - q s, \qquad c = p s + q r .$$

That is, every integer solution of the equal-sums-of-two-squares equation is produced by the four parameters $p,q,r,s$ in the pattern of the Brahmagupta–Fibonacci / four-parameter identity, up to possibly interchanging the roles of the two entries $c$ and $d$ on the right-hand side (branch 2 is branch 1 with $c$ and $d$ swapped; note $b = ps - qr$ keeps its form in both branches, and the two branches share the witnesses' formula for $a$).

No size bound, coprimality, positivity or normality is imposed on $a,b,c,d$ or on $p,q,r,s$; the witnesses are asserted only to exist, never uniquely. Degenerate solutions are expressly covered by the quantifiers: $a=b=c=d=0$ (take $p=q=r=s=0$ in either branch), solutions with zero entries, negative entries, coincident entries, and solutions where one side is empty of squares ($c=d=0$, forcing $a=b=0$). Note that the bound $a^2+b^2 = c^2+d^2$ alone is *not* always realisable in branch 1 — e.g. $(a,b,c,d) = (1,8,4,7)$ has $a+c = 5$ odd, which makes $2pr = a+c$ impossible over the integers; for such quadruples only branch 2 can (and, by the theorem, does) succeed — with $p=2, q=-1, r=2, s=3$ giving $pr+qs = 1 = a$, $ps-qr = 8 = b$, $pr-qs = 7 = d$, $ps+qr = 4 = c$. Both branches are therefore needed, and neither is vacuous.

## Audit notes

- **Truth.** TRUE, and this is the delicate item; it was checked in two independent ways.

  *Mathematical proof.* Suppose $a^2+b^2 = c^2+d^2$. Counting odd entries modulo $4$ (every odd square is $\equiv 1 \pmod 4$ and every even square $\equiv 0 \pmod 4$) shows that the number of odd entries among $\{a,b\}$ equals the number of odd entries among $\{c,d\}$, whence either (i) $a-c$ and $b-d$ are both even, or (ii) $a-d$ and $b-c$ are both even.

  *Case (i).* Set $X = (a+c)/2$, $Y = (a-c)/2$, $U = (b+d)/2$, $V = (d-b)/2$; these are integers, they satisfy $X+Y=a$, $X-Y=c$, $U-V=b$, $U+V=d$, and $XY = \frac{a^2-c^2}{4} = \frac{d^2-b^2}{4} = UV$. Applying the four-factor parametrisation (valid for all integer solutions of $XY = UV$, including all zero patterns) gives $p,q,r,s$ with $X = pr$, $Y = qs$, $U = ps$, $V = qr$; substituting back yields exactly branch 1:
  $a = X+Y = pr+qs$, $c = X-Y = pr-qs$, $b = U-V = ps-qr$, $d = U+V = ps+qr$.

  *Case (ii).* Same construction with $c$ and $d$ interchanged: $X = (a+d)/2$, $Y = (a-d)/2$, $U = (b+c)/2$, $V = (c-b)/2$, giving $a = pr+qs$, $d = pr-qs$, $b = ps-qr$, $c = ps+qr$, i.e. branch 2.

  *Machine verification.* For every quadruple with $a,b,c,d \in [-30,30]$ satisfying $a^2+b^2 = c^2+d^2$ (40 001 quadruples), explicit integer witnesses $p,q,r,s$ were constructed by the above route and then re-verified against the four claimed equalities: **zero unresolved quadruples**. Concrete checked examples: $(1,8,4,7) \mapsto$ branch 2 with $(p,q,r,s) = (2,-1,2,3)$; $(1,7,5,5)$ ($1+49 = 25+25$) $\mapsto$ branch 1; $(0,0,0,0) \mapsto$ either branch with all parameters $0$.
- **Faithfulness.** Name matches file name. The doc line's claim that "the four-parameter parametrisation is complete" is rendered as: *every* solution arises from some $(p,q,r,s)$, *up to swapping $c$ and $d$* — and the second branch is present precisely for that swap, so no case is dropped. All variables are bound: $a,b,c,d$ are implicit universal arguments, $p,q,r,s$ are existentially bound inside each branch, and every one appears in the branch's equations; nothing is free and nothing is quantified over vacuously. The statement is one-directional (every solution *comes from* parameters) and deliberately does not include the converse direction (that every choice of parameters yields a solution) — that direction is the content of the separate item `four_param_identity`; if the author's notion of "completeness" was intended to bundle both directions, this item alone supplies only the completeness half.
- **Trivializing premise.** None: the single hypothesis is the equation under study, not a restatement of the parametrisation; it is not contradictory and does not restrict to degenerate solutions. The two-branch disjunction is genuinely required (see the $(1,8,4,7)$ example, where branch 1 is impossible), so the disjunction is not padding.
- **Satisfiability.** The hypothesis is satisfiable with abundant non-trivial witnesses — every member of the explicit family $(1, n^2-n+1, 2n-1, n^2-n-1)$, plus $(1,7,5,5)$, $(1,8,4,7)$, $(1,8,7,4)$ etc. — so the theorem is emphatically non-vacuous.
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
