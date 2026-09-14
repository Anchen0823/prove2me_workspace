# Upstream error-bound reuse audit

Revision: `a5154676af9aa3095150ee410cdda80555aa0642` of AlexKontorovich/PrimeNumberTheoremAnd. These are source audits, not local builds of the upstream project.

The secondary blueprint's completed-looking wrappers do not provide unconditional replacements for the remaining prime-estimate obligations:

1. `RS_prime.theorem_a` calls `RS_prime.theorem_12`; the latter is `by sorry` at `IEANTN/RosserSchoenfeld/RosserSchoenfeldPrime.lean:1015`.
2. `Dusart1999.theorem_a`, giving `|psi x - x| <= 0.006409*x/log x` for `x >= exp 22`, uses its private `theta_err`, which calls `BKLNW.thm_1b_table`. That table theorem is `by sorry` at `IEANTN/BKLNW/BKLNW.lean:2183`. Moreover its threshold is higher than the original leaf's `10^8`, so even a complete version would need an additional intervening-range proof.
3. The Buthe square-root estimate for `11 < x <= 10^19` is itself `by sorry` at `IEANTN/Buthe.lean:33`.

Exact fetched source snapshots are stored under `continuation/upstream-*.lean`. No theorem depending on these holes has been submitted as a completed proof. This audit rules out these specific reuse candidates; it does not establish that no suitable complete formalization exists elsewhere.

Primary sources:

- https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/IEANTN/BKLNW/BKLNW.lean#L2183
- https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/IEANTN/Buthe.lean#L33
- https://alexkontorovich.github.io/PrimeNumberTheoremAnd/blueprint/secondary-chapter.html
