# Read-back: `family_primitive`

Declared in namespace `EqualTwoSquares` (file `items/family_primitive.lean`); the name agrees with the file name. Its own doc line reads *"Every member of the family is primitive: the four entries have gcd one."*

## What the declaration literally says

For every integer $n \in \mathbb{Z}$, with

$$a = 1,\qquad b = n^2 - n + 1,\qquad c = 2n - 1,\qquad d = n^2 - n - 1,$$

the iterated greatest common divisor satisfies

$$\gcd\!\bigl(\gcd(a,b),\; \gcd(c,d)\bigr) \;=\; 1 ,$$

i.e. the gcd of all four entries of the member of the family indexed by $n$ equals $1$. (In the source the first inner gcd, whose value is a natural number, is coerced back to integers before being fed to the outer gcd; the value compared to $1$ is therefore a natural number, and both inner gcds use absolute values, so signs of the entries are irrelevant.)

There is no hypothesis: every integer $n$, positive, negative or zero, is covered, including the members where entries repeat ($n = 0$: entries $1,1,-1,-1$; $n = 1$: entries $1,1,1,-1$).

Note also that the conclusion is *exactly* the assertion that the four entries are collectively coprime; it is **not** the stronger statement that they are pairwise coprime, and not the statement $\gcd(a,b)=\gcd(c,d)=1$ separately. It also says nothing about the family being primitive in the sense usually needed downstream (e.g. it does not rule out a common divisor of three of the four entries).

## Audit notes

- **Truth.** TRUE, and verified for all $|n| \le 200$ by direct gcd computation. **However, the auditor should be aware that the statement is contentless as written:** because the first entry is the constant $1$, one has $\gcd(1,\, n^2-n+1) = 1$ for every $n$, hence the outer gcd is $\gcd(1,\; \gcd(2n-1,\, n^2-n-1)) = 1$ identically. The displayed equality therefore reduces to $1 = 1$ independently of $n$ and independently of any property of the family beyond "the first entry is $1$". This is a weakness of the statement's *informative value* (it carries no mathematical content about the parametrisation), not a defect of truth or of wording: the statement says what it claims to say, and it is true.
- **Faithfulness.** Name matches file name. The doc line "the four entries have gcd one" is precisely what the iterated gcd expression asserts (the nesting order pairwise-then-global computes the gcd of all four). Variables: only $n$, explicit, occurring in three of the four entries; nothing free. **Caveat flagged above: the item is trivially true because of the normalised first coordinate $1$.**
- **Trivializing premise.** None: there is no hypothesis at all. The triviality comes from the *conclusion's* structure, not from a premise.
- **Satisfiability.** No hypothesis; non-vacuous.
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
