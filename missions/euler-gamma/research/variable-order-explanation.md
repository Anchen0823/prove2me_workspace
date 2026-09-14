This is a complete, unconditional proof of a method-specific upper bound, not a proof of irrationality of Euler's constant.

For integers n >= 1 and p >= 0 define

$$c_{n,p,k}=\binom nk^2\binom{n+k}k^p/k!,\qquad Q_{n,p}=\sum_{k=0}^n c_{n,p,k},$$
$$P_{n,p}=-\sum_{k=0}^n c_{n,p,k}\bigl(pH_{n+k}+2H_{n-k}-(p+3)H_k\bigr).$$

The theorem proves

$$P_{n,p}/Q_{n,p}\le 3H_n-p/2.$$

Proof: for 0 <= k <= n, each of the n summands in H_(n+k)-H_k is at least 1/(2n), so the difference is at least 1/2. Also H_k <= H_n and H_(n-k) >= 0. Consequently

$$pH_{n+k}+2H_{n-k}-(p+3)H_k
=p(H_{n+k}-H_k)+2H_{n-k}-3H_k\ge p/2-3H_n.$$

All weights are nonnegative and c_(n,p,0)=1, so Q_(n,p)>0. Summing the inequalities and dividing by Q proves the assertion. The Lean proof includes positivity of Q and uses no platform theorem imports or unproved analytic assumptions.

In particular, if p >= 6H_n, then P/Q <= 0. Since gamma > 1/2, such orders cannot give positive rational approximants converging to gamma. Thus a variable-order search in this explicit family must keep p < 6H_n at indices where its approximants are positive. Using H_n <= 1+log n gives the necessary O(log n) scale. This does not exclude smaller growing orders, other families, or exceptional subsequences.

Provenance: the denominator family is Van Assche--Wolfs, arXiv:2404.09799v3, Section 5, displayed formula for F_(n;2)^(I|p)(1). The explicit numerator is obtained by the differential-operator iteration in that section (the p=2 case matches Prove2Me's eulerMascheroni_p2Approximation definition). The upper bound above was derived in this research session, 2026-09-14; it is not claimed to be a theorem stated in that paper or a literature-priority result. The formal theorem is purely about the displayed finite sums and does not depend on establishing a contour representation or their convergence to gamma.

Scope of contribution: a proved obstruction to excessive variable order, with no claim to resolve the mission root, the P2 primitive-saving conjecture, or the irrationality milestone.
