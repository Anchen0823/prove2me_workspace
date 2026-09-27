## Motivation

The **representation function** $r_{2}(n)=\#\{(a,b)\in\mathbb Z^{2}:a^{2}+b^{2}=n\}$ is one of the oldest objects in number theory. Fermat characterised the integers with $r_{2}(n)>0$ — those in which every prime congruent to $3$ modulo $4$ occurs to an even power — and Euler's proof supplied the closed form $r_{2}(n)=4\,(d_{1}(n)-d_{3}(n))$, where $d_{j}(n)$ counts divisors congruent to $j$ modulo $4$ ([sum of two squares theorem](https://en.wikipedia.org/wiki/Sum_of_two_squares_theorem)).

That description counts representations but does not relate them to one another. The integers carrying several *essentially different* representations,

$$
50=1^{2}+7^{2}=5^{2}+5^{2},\qquad 65=1^{2}+8^{2}=4^{2}+7^{2},
$$

are exactly the integers that produce quadruples $(a,b,c,d)$ with

$$
a^{2}+b^{2}=c^{2}+d^{2}
$$

whose two sides are not identified by swapping the two entries or changing their signs. Three reasons make this relation worth a formal development rather than a passing remark.

* **Energy counts.** Counting solutions of the equation inside a box is the additive energy of the set of sums of two squares, the quantity controlling mean-square errors for $r_{2}$; it is a genuinely different problem from determining $r_{2}(n)$ for a single $n$, and every estimate for it starts from a description of the solution set.
* **Composition of representations.** The [Brahmagupta–Fibonacci identity](https://en.wikipedia.org/wiki/Brahmagupta%E2%80%93Fibonacci_identity)

  $$
  (p^{2}+q^{2})(r^{2}+s^{2})=(pr+qs)^{2}+(ps-qr)^{2}=(pr-qs)^{2}+(ps+qr)^{2}
  $$

  takes two representations and produces a third. Known to Brahmagupta and stated by Fibonacci in *Liber Quadratorum* (1225), it is the multiplicativity of the norm in the Gaussian integers, and it is the engine behind every statement below.
* **Geometry.** Over a field, the locus $a^{2}+b^{2}=c^{2}+d^{2}$ in projective three-space is the split quadric, isomorphic to $\mathbb P^{1}\times\mathbb P^{1}$ under the [Segre embedding](https://en.wikipedia.org/wiki/Segre_embedding); the four parameters introduced below are Segre coordinates in this sense. The arithmetic content of the equation is precisely the integrality that this geometry ignores.

The parametrisation targeted here is classical. Nothing in this mission claims new mathematics; the aim is a machine-checked development in which every hypothesis is explicit.

## Setting

Fix integers. A **solution** is a quadruple $(a,b,c,d)\in\mathbb Z^{4}$ with $a^{2}+b^{2}=c^{2}+d^{2}$. It is **trivial** if the multisets $\{a^{2},b^{2}\}$ and $\{c^{2},d^{2}\}$ coincide, i.e. if $(c,d)$ equals $\pm(a,b)$ or $\pm(b,a)$; if entries are allowed to vanish, the least value carried by a non-trivial solution is $25=0^{2}+5^{2}=3^{2}+4^{2}$, and requiring all four entries to be positive raises that value to $50$. A solution is **primitive** when the four entries have greatest common divisor $1$, and **positive** when all four entries are positive and pairwise distinct — the case in which nothing about the relation is explained by signs, zeros or coincidences.

Two constructions produce solutions. The **four-parameter family** associates to integers $p,q,r,s$ the quadruple

$$
a=pr+qs,\qquad b=ps-qr,\qquad c=pr-qs,\qquad d=ps+qr,
$$

which solves the equation because both sides equal $(p^{2}+q^{2})(r^{2}+s^{2})$ by the identity above. Substituting particular parameters is unrevealing, so a genuine supply comes instead from the elementary one-parameter family

$$
1^{2}+(n^{2}-n+1)^{2}=(2n-1)^{2}+(n^{2}-n-1)^{2},
$$

whose four entries $1$, $n^{2}-n+1$, $2n-1$, $n^{2}-n-1$ are strictly increasing — hence positive and pairwise distinct — as soon as $n\ge 4$. The bound is sharp: at $n=3$ the two entries $2n-1$ and $n^{2}-n-1$ are equal.

In the reverse direction, rewrite the equation as $(a+c)(a-c)=(d+b)(d-b)$ and set

$$
X=(a+c)/2,\quad Y=(a-c)/2,\qquad U=(b+d)/2,\quad V=(d-b)/2 .
$$

The halves are integers exactly when $a$ and $c$ share a parity and so do $b$ and $d$, and in that case the equation becomes

$$
XY=UV .
$$

The development is organised in the namespace `TwoSquares`, with node names matching the roles above (`four_param_identity`, `explicit_family_chain`, `sum_sq_eq_halves`, `four_factor_param`, `complete_parametrization`).

## Formalization targets

### Goal — completeness of the four-parameter family

For all integers $a,b,c,d$ with $a^{2}+b^{2}=c^{2}+d^{2}$, there are integers $p,q,r,s$ with

$$
a=pr+qs,\quad b=ps-qr,\quad c=pr-qs,\quad d=ps+qr,
$$

possibly after interchanging $c$ and $d$. The goal asserts only the existence of integral parameters and the necessity of at most one swap; it does not assert uniqueness of $(p,q,r,s)$, which is false, and it says nothing about how many solutions lie in a given box.

### The four-parameter identity

The identity itself, over an arbitrary commutative ring, together with the two forms of the Brahmagupta–Fibonacci identity that imply it — so that the reason it holds, rather than the expansion, is what is recorded.

### An explicit infinite family

For every integer $n\ge 4$ the displayed family is a positive pairwise distinct solution; the parametrisation $n\mapsto(1,\,n^{2}-n+1,\,2n-1,\,n^{2}-n-1)$ is injective; the set of quadruples it produces is infinite; and no member is a nontrivial integer multiple of another, each member being primitive.

### From the sum-of-squares equation to $XY=UV$

The equivalence of $a^{2}+b^{2}=c^{2}+d^{2}$ with $(a+c)(a-c)=(d+b)(d-b)$; the parity statement that matching entries share a parity after at most one swap; and the resulting existence of the half-sum variables satisfying $XY=UV$.

### Parametrizing $XY=UV$

For all integers $X,Y,U,V$ with $XY=UV$ there are integers $p,q,r,s$ with $X=pr$, $Y=qs$, $U=ps$, $V=qr$ — the coordinate form of the statement that a rank-one $2\times2$ matrix factors through the integers.

## Significance

*The result.* Taken together, the reverse chain converts the Diophantine equation $a^{2}+b^{2}=c^{2}+d^{2}$ into four free integer parameters, at the cost of one possible swap. In that form every question about the solution set becomes a question about four independent variables, which is what makes energy estimates, density statements and searches for primitive solutions tractable. The chain also isolates where integrality enters: over a field the parametrisation of $XY=UV$ is formal, so the content is carried entirely by the parity step and by divisibility over $\mathbb Z$.

*Formalizing it.* None of the mathematics is new, and that is the point: the value here is a development in which each link is a reusable statement with explicit hypotheses. Three conventions make the nodes reusable rather than bespoke. The algebraic identity is proved over a general commutative ring, not over $\mathbb Z$. The positivity and distinctness of a family are packaged as one strict chain rather than as a list of inequalities, since later arguments use the ordering, not merely the disequalities. The parity issue is isolated into a single node stating a disjunction, instead of being discharged by case splits buried inside a later proof. Conversely, the shape of the final theorem records honestly what is not claimed: parameters are not unique, and no normal form is asserted.

As difficulty, the early nodes have short proofs, while completeness requires the full chain and is the substantial part of the mission.

## Difficulty

The obvious first idea is to use the Gaussian integers: $a+bi$ and $c+di$ have the same norm, so factor both and compare. It fails. Equal norm does not make two Gaussian integers associates or divisors of one another — $1+8i$ and $4+7i$ both have norm $65$ and are related by no divisibility — because uniqueness of factorisation regroups prime factors in ways that the norm alone cannot distinguish. The correct route recovers the four parameters from the *product* equation instead, and there the friction is entirely arithmetic:

*Clearing halves.* The substitution $X=(a+c)/2$ is not available for arbitrary solutions: $a^{2}+b^{2}=c^{2}+d^{2}$ forces only that the *multiset* of parities of $(a,b)$ matches that of $(c,d)$, so $(a,c)$ may have different parities and no integer $X$ may exist. The example $a=1,b=0,c=0,d=1$ shows this is not vacuous, and it is why the goal carries a swap.

*Factoring $XY=UV$.* Taking $p=\gcd(X,U)$ yields $X=pr$, $U=ps$ with $\gcd(r,s)=1$, and Euclid's lemma then forces $s\mid Y$ and $r\mid V$. The degenerate case $X=U=0$ — where the gcd vanishes and no cancellation is possible — must be handled separately, and because the variables range over $\mathbb Z$ rather than $\mathbb N$, every divisibility step must be tracked with signs. Working over a ring where division is available would delete both issues and with them the entire content of the statement.

## Formalization scope

* All nodes are stated over $\mathbb Z$, except the Brahmagupta–Fibonacci identity and the four-parameter identity, which are proved over an arbitrary commutative ring. No node is stated over $\mathbb N$; transporting the prime-level statements is out of scope.
* Gaussian integers are deliberately unused. Mathlib carries them, but nothing here needs them, and a development depending on them would obscure the arithmetic that actually carries the proof.
* No quotient types, no permutation machinery: the possible swap of $c$ and $d$ is expressed as a disjunction, and the parity statement as a disjunction over `Even`.
* *Trivializing formalizations are excluded.* Over a field the parametrisation of $XY=UV$ holds trivially (take $p=X$, $r=1$, $s=U/X$), so the quarter-ring version carries no information; likewise, a completeness statement whose hypotheses already postulate the existence of the parameters would be vacuous. Both are explicitly not what is asked for.
* Expected to be reusable beyond this mission: the two forms of the Brahmagupta–Fibonacci identity; the strict-chain packaging of positivity and distinctness for a family given by polynomials; and the integer parametrisation of $XY=UV$, which is the Segre parametrization.
* Contributions are welcome for any node, and especially for the integer factoring lemma, for which several proofs are available. Explicitly **out of scope**: uniqueness or normal forms for $(p,q,r,s)$, counting asymptotics for solutions in a box, the Gaussian-integer reformulation, and all $\mathbb N$-level variants.

## Selected references

- [Sum of two squares theorem](https://en.wikipedia.org/wiki/Sum_of_two_squares_theorem) — Fermat's characterisation and Euler's divisor formula for $r_{2}$.
- [Brahmagupta–Fibonacci identity](https://en.wikipedia.org/wiki/Brahmagupta%E2%80%93Fibonacci_identity) — the two-square composition identity, its history, and its interpretation through norms.
- Leonardo Pisano (Fibonacci), *Liber Quadratorum*, 1225. English translation: L. E. Sigler, *The Book of Squares*, Academic Press, 1987.
- G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 6th ed., Oxford University Press, 2008 — Chapter XX on representations by two squares.
- [Segre embedding](https://en.wikipedia.org/wiki/Segre_embedding) — the identification of the rank-one quadric in $\mathbb P^{3}$ with $\mathbb P^{1}\times\mathbb P^{1}$.
