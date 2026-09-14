For every positive integer $n$,
$$0<I_n<16^{-n}.$$
Put $b=x(1-x)y(1-y)$ and let $K_n$ be the integrand. On the open unit square, the strict logarithm inequality
$$-\log t>\frac{2(1-t)}{1+t}$$
and $(1-x^2)(1-y^2)\le(1-xy)^2$ imply
$$K_1(x,y)<\frac{xy}{4}.$$
Since $0<b\le1/16$, it follows that
$$0<K_n(x,y)=b^{n-1}K_1(x,y)<16^{-(n-1)}\frac{xy}{4}.$$
The kernel is measurable and bounded on the open square. Its sections and their integrals are integrable; endpoints have measure zero. Strict integration first in $y$, then in $x$, gives the claimed upper bound, since the double integral of $xy/4$ is $1/16$. Positivity on the open square gives the lower bound. This proves the integral estimate without using the gamma integral identity or any open theorem.
