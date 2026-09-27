# Read-back: `four_factor_param`

Declared in namespace `EqualTwoSquares` (file `items/four_factor_param.lean`); the name agrees with the file name. Its own doc line reads *"Objective 5: every solution of XY = UV over the integers admits four parameters."*

## What the declaration literally says

For all integers $X, Y, U, V \in \mathbb{Z}$ satisfying the single hypothesis

$$X \cdot Y \;=\; U \cdot V ,$$

there exist integers $p, q, r, s$ such that all four factorisations hold simultaneously:

$$X = p r, \qquad Y = q s, \qquad U = p s, \qquad V = q r .$$

(Schematically: the four quantities are the $2 \times 2$ "cross products" of the parameters, arranged as $\begin{smallmatrix}X = pr & U = ps\\ V = qr & Y = qs\end{smallmatrix}$.) There is no coprimality condition, no positivity, no non-vanishing, no bound on the size of $p,q,r,s$, and no uniqueness claim: witnesses are asserted to exist, nothing more. All four of $X,Y,U,V$ are explicit arguments and all four appear in the hypothesis and in the conclusion.

Degenerate cases are explicitly covered by the quantifiers, and they were the focus of the counterexample hunt: all four variables $0$; exactly three zero; exactly two zero on the same "diagonal" (e.g. $X = U = 0$ with $Y, V$ arbitrary); two zero on the same "side" (e.g. $X = Y = 0$ forcing $U = 0$ or $V = 0$); negative values (e.g. $X = 2, Y = 0, U = -3, V = 0$); coincidences such as $X=Y=U=V=2$; and cases where $\gcd$ of two of the variables is $0$, which happens exactly when both are $0$. A worked example of the verification below: $X = 2, Y = 0, U = 3, V = 0$ is realised by $p=1, q=0, r=2, s=3$ (indeed $pr = 2 = X$, $ps = 3 = U$, $qs = 0 = Y$, $qr = 0 = V$); $X=0,Y=0,U=1,V=0$ by $p=1,q=0,r=0,s=1$.

## Audit notes

- **Truth.** TRUE. General proof: if $X = U = 0$, take $p = 0$, $q = 1$, $r = V$, $s = Y$ (then $pr = 0 = X$, $ps = 0 = U$, $qs = Y$, $qr = V$). Otherwise let $g = \gcd(X,U) > 0$, put $p = g$, $r = X/g$, $s = U/g$, so $X = pr$, $U = ps$ and $\gcd(r,s)=1$; the hypothesis gives $g\,r Y = g\,s V$, hence $rY = sV$ (as $g \neq 0$); if $r = 0$ then $X = 0$, so $s = \pm 1$ and $V = 0$, and one takes $q = Y/s$; if $r \neq 0$, coprimality gives $r \mid V$, say $V = qr$, and then $rY = rqs$ gives $Y = qs$. Signs do not obstruct anything since $g > 0$ and divisibility over $\mathbb{Z}$ is up to sign. Additionally: (a) every quadruple with $X Y = U V$ and all entries in $[-14,14]$ was checked against the explicit construction — 7905 tuples, 0 failures; (b) an independent brute-force search for witnesses (not using any construction) over all quadruples in $[-6,6]^4$ and witnesses in $[-40,40]^4$ found witnesses for all 1313 admissible tuples, 0 failures. **No counterexample exists among the flagged danger zones: multiple zeros, $\gcd = 0$ (i.e. $X = U = 0$), and negative values.**
- **Faithfulness.** Name matches file name; the doc line matches the statement precisely ("every solution of $XY = UV$ admits four parameters"). Every variable is bound (four explicit parameters $X,Y,U,V$ plus four existentially bound witnesses); nothing free, and every variable mentioned in the conclusion is quantified.
- **Trivializing premise.** None: $X Y = U V$ is the object of study, not a restatement of the existence of $p,q,r,s$. Interesting cases abound (e.g. $X=1,Y=6,U=2,V=3$ forces witnesses $p=1,q=3,r=1,s=2$), so the statement is not vacuous or empty in its interesting case.
- **Satisfiability.** Satisfiable with many witnesses, both degenerate ($X=Y=U=V=0$, realised by $p=q=r=s=0$) and genuinely non-trivial ($X=6,Y=10,U=15,V=4$, realised by $p=3,q=2,r=2,s=5$). Non-vacuous.
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
