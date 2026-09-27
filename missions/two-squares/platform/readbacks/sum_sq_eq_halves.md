# Read-back: `sum_sq_eq_halves`

Declared in namespace `EqualTwoSquares` (file `items/sum_sq_eq_halves.lean`); the name agrees with the file name. Its own doc line reads *"Objective 4, substitution: under parity alignment the equation becomes XY = UV."*

## What the declaration literally says

Let $a, b, c, d \in \mathbb{Z}$ be integers subject to three hypotheses:

1. $a^2 + b^2 = c^2 + d^2$ (the sum-of-two-squares equation);
2. $a - c$ is even;
3. $b - d$ is even.

Then there exist integers $X, Y, U, V$ satisfying all five of the following simultaneously:

$$X + Y = a, \qquad X - Y = c, \qquad U - V = b, \qquad U + V = d, \qquad X \cdot Y \;=\; U \cdot V .$$

"Even" here means divisible by $2$ in $\mathbb{Z}$ ($n = 2k$ for some integer $k$; negative differences and zero count as even). Note that no division appears in the statement: the "halves" are captured implicitly by the four linear equations, which say

$$X = \tfrac{a+c}{2},\quad Y = \tfrac{a-c}{2},\quad U = \tfrac{b+d}{2},\quad V = \tfrac{d-b}{2},$$

and it is precisely hypotheses 2 and 3 that guarantee these four quantities are integers: $a - c$ even implies $a + c = (a-c) + 2c$ is even, so $X, Y$ exist with $X+Y=a$, $X-Y=c$; likewise $b - d$ even implies $b + d$ even, so $U, V$ exist with $U-V=b$, $U+V=d$. Note the asymmetry in the third and fourth equations: $U - V = b$ while $U + V = d$, i.e. $V = (d-b)/2$ and $U = (b+d)/2$ — this matches the substitution convention $U = (b+d)/2$, $V = (d-b)/2$.

The product identity then follows from hypothesis 1: $X Y = \frac{a^2-c^2}{4}$ and $U V = \frac{d^2 - b^2}{4}$, and $a^2 - c^2 = d^2 - b^2$ is a rearrangement of $a^2+b^2 = c^2+d^2$.

Everything degenerate is covered: $a=b=c=d=0$ (take $X=Y=U=V=0$), non-positive entries, coincident entries, and cases where some of $X,Y,U,V$ vanish (e.g. $a = c = 0$ forces $X = Y = 0$ and then $U V = 0$).

## Audit notes

- **Truth.** TRUE. Existence of the four witnesses is exactly the divisibility-by-$2$ discussion above (hypotheses 2 and 3 are precisely what is needed, and no more), and the final equation is the rearrangement of hypothesis 1 just displayed. Verified exhaustively: for every quadruple with $a,b,c,d \in [-12,12]$ satisfying $a^2+b^2 = c^2+d^2$ together with evenness of $a-c$ and $b-d$, the explicit witnesses $X = (a+c)/2$, $Y=(a-c)/2$, $U=(b+d)/2$, $V=(d-b)/2$ satisfy all five conclusions — zero failures.
- **Faithfulness.** Name matches file name; the doc line "under parity alignment the equation becomes $XY = UV$" is rendered literally: the two evenness hypotheses are the parity alignment (only its first branch; the swap branch is not needed here), and the conclusion supplies $X,Y,U,V$ together with $XY = UV$. All variables are bound: $a,b,c,d$ are implicit arguments, $X,Y,U,V$ are existentially bound; every one of them occurs in the conclusion, so none is unconstrained.
- **Trivializing premise.** None: the evenness hypotheses are not the conclusion (the conclusion is the existence of witnesses together with a product equation), they are not contradictory, and they do not single out only trivial instances of the sum-of-squares equation. Note also that these hypotheses do restrict the instances (the branch where $a-c$ and $b-d$ are both odd is excluded), but the remaining family of instances is still rich — e.g. $(a,b,c,d) = (1,8,7,4)$ satisfies all three hypotheses.
- **Satisfiability.** All three hypotheses are simultaneously satisfiable, in trivial and non-trivial ways: $(0,0,0,0)$; $(1,8,7,4)$ ($1+64 = 49+16$, $a-c = -6$ even, $b-d = 4$ even, realised by $X=4,Y=-3,U=6,V=-2$ with $XY = -12 = UV$). Non-vacuous, infinitely many witnesses.
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
