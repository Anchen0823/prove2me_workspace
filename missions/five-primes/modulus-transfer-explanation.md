# Direct modulus transfer proof

For $x\ge 10^{20}$ and positive $q_0$ whose prime factors are at most $\sqrt{x}$, we prove the stronger estimate

$$\left|S_{\eta_0,q_0}(x,\alpha)-S_{\eta_0,2}(x,\alpha)\right|\le 18\sqrt{x}\le 20.16\sqrt{x}.$$

The coprimality indicators differ only at integers not coprime to $2q_0$, and their difference has absolute value at most one. The cutoff satisfies $0\le\eta_0\le3$ and vanishes for arguments at least one. Truncating the sums at $\lfloor x\rfloor$ therefore bounds the difference by three times the von Mangoldt mass of those exceptional integers.

Every exceptional prime divides $2q_0$ and hence is at most $\sqrt{x}$. The exceptional nonprime mass is bounded by the entire nonprime von Mangoldt mass. Consequently,

$$|S_{\eta_0,q_0}-S_{\eta_0,2}|\le 3\bigl(\theta(\sqrt{x})+\psi(x)-\theta(x)\bigr).$$

Mathlib's elementary Chebyshev bounds give

$$\theta(t)\le(\log4)t\le2t,\qquad \psi(t)\le6t.$$

For $t\ge4096$, the sharper bound $\psi(t)\le(\log4)t+2\sqrt{t}\log t$ implies $\psi(t)\le3t$: use $\log t\le4t^{1/4}$ and $t^{1/4}\ge8$.

The prime-power decomposition supplied by Mathlib gives

$$\psi(x)-\theta(x)\le\psi(x^{1/2})+\psi(x^{1/3})+\psi(x^{1/5}).$$

Here $\sqrt{x}\ge4096$, $x^{1/5}\le x^{1/3}$, and $12x^{1/3}\le\sqrt{x}$, since $x\ge10^{20}>12^6$. Thus

$$\psi(x)-\theta(x)\le3\sqrt{x}+6x^{1/3}+6x^{1/5}\le4\sqrt{x}.$$

Combining these inequalities gives the claimed $18\sqrt{x}$ bound. The Lean proof imports only Mathlib and the two definitions of the smoothed sum and cutoff; it has no open theorem dependencies.

The cutoff and finite-sum bookkeeping adapt portions of marwahaha's accepted proof of `TaoFivePrimes.eta0_primorial_sieve_transfer` (submission `0effebaf-7763-4c9a-af01-2a79c0b6e739`). The direct indicator comparison and explicit square-root prime-power estimate provide the bound needed here.
