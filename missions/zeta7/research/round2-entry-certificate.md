# An independent finite integerization certificate

This is a finite, coefficientwise theorem. It does not prove an asymptotic
decay estimate or irrationality of any zeta value.

Let `G(X)=A+XB` be the rational symmetric matrix constructed by
`exact_hankel.py`, with odd `s>=3`, simple remaining poles at `-j²`, and
nonnegative monomial exponents `e_i`. Let `Delta=det G` and let `P=c Delta`
be its positive primitive integer multiple (`c>0`). Positive definiteness
at zeta(s) ensures that Delta is nonzero.

## 1. Finite prime support

If the numerator before cancellation has degree `d`, set

```
E=max(0,d-K+2 max_i e_i),
L=max(2K,2E+3,s-1).
```

Every entry of A and B is integral at all primes `p>L`:

- Division by a monic integral polynomial introduces no denominators.
- A simple-pole residue divides a product of differences `j²-l²`; each
  prime divisor is at most `2K`.
- Pole constants have denominators from `H_j^(s)`, `s-1`, and `2j`.
- By von Staudt--Clausen, a denominator prime of `B_(2e+2)` satisfies
  `p-1 | 2e+2`, hence `p<=2e+3`. The extra denominator `(s-1)!` has primes
  at most `s-1`. Here every polynomial moment has degree at most E.

This bounds denominator primes only. Numerator content can have larger
prime factors; the certificate does not assume otherwise.

## 2. Matching lower bound with an exact witness

For every prime `p<=L`, define

```
w_ij=min(v_p(A_ij),v_p(B_ij)),  v_p(0)=+infinity,
l_p=min_permutation pi sum_i w_(i,pi(i)).
```

Each product in the determinant expansion is a polynomial whose every
coefficient has valuation at least its matching weight. Adding these
products cannot decrease the minimum valuation. Therefore

```
v_p([X^k]Delta)>=l_p  for every k.
```

The script computes the minimum with integer Hungarian arithmetic and
stores a permutation pi and integer row/column potentials u,v satisfying

```
u_i+v_j<=w_ij,
sum_i w_(i,pi(i))=sum_i u_i+sum_j v_j.
```

These inequalities certify optimality without trusting a floating optimizer.
For both-zero entries the implementation uses a finite sentinel
`(2h+1)M+1`, where M bounds the absolute finite weights. The diagonal
matching is finite, since positive Gram diagonal entries cannot be identically
zero. Any matching using the sentinel costs more than this finite matching,
so the computed optimum never uses a both-zero entry.

Consequently the positive rational number

```
t=product_(p<=L) p^(-l_p)
```

satisfies **t Delta in Z[X]**. Negative l_p contributes to the numerator
of t; positive l_p removes proven common content. The proof covers all
coefficients including the constant coefficient, and all small primes.

## 3. Primitive gap and changing basis

Since P is primitive, any rational r with rP integral is an integer
(Bezout applied to its coefficients). Thus

```
t/c is a positive integer,
g_K=log(t/c)/K²>=0.
```

The program independently reconstructs Delta, verifies every local bound
against its exact coefficients, and checks this final integer ratio. This
is a true finite comparison; replacing t by an exponential of an asymptotic
constant would not justify these checks.

For a whole shifted block, a second certificate uses the monic integral
polynomial basis `u_0=1`, `u_i=t product_(j=1)^(i-1)(t+j²)`. Its coefficient
matrix T is unit lower triangular. Applying `T A T^T, T B T^T` leaves Delta
unchanged but can improve the entrywise valuation bound. This improves an
estimate of the same primitive polynomial, not the primitive polynomial
itself.

## 4. Finite results for the selected profiles

The layers are `(N_a/K,q_a)=(3/40,1),(6/40,3)` and `h/K=1/2`.
The displayed decimals come from saved Arb intervals.

| shift g/K | K | raw monomial gap | Newton-basis gap |
|---|---:|---:|---:|
| 0 | 40 | 2.47427757 | 1.31848788 |
| 0 | 80 | 3.08157882 | 1.47445286 |
| 1/40 | 40 | 2.58377382 | 1.37465444 |
| 1/40 | 80 | 3.20848733 | 1.54862500 |

The bound is valid but loose. A separate structured residue/CRT bound is
studied in `round2-arithmetic.md`; it should not be confused with this
entrywise certificate. None of these finite gaps bounds an asymptotic gap.

Reproduce with `scripts/round2_entry_certificate.py`, choosing
`--basis monomial` or `--basis newton`. Saved witnesses are
`verification/round2-entry-certificates.json` and
`verification/round2-newton-certificates.json`.
