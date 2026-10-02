For an ALGORITHM 2 trace with integer parameter $k\ge2$, parameter $0<g\le1$, and at least one executed iteration, we establish the following reduction of the iteration bound:

$$t\le\frac{\log SIZE(I_0)}{\log k}+1.$$

Here $I_0$ denotes the instance after the initial removal of small items. The only imported theorem assumption is the existing milestone `alg2_size_recursion`, which is still open. This submission proves the passage from that one-step recurrence to the logarithmic bound; it does not independently prove the recurrence.

Set

$$S_i=SIZE(I_i),\qquad L=\log(1/g),\qquad C=\frac{L}{1-1/k}.$$

The parameter assumptions imply that $C$ is nonnegative. The recurrence milestone supplies

$$S_{i+1}\le S_i/k+L\qquad(i<t).$$

Since $C/k+L=C$, induction gives

$$S_i\le S_0/k^i+C\qquad(i\le t).$$

The last executed iteration has index $t-1$. Its loop condition, together with the geometric bound, gives

$$1+C<S_{t-1}\le S_0/k^{t-1}+C,$$

and therefore

$$k^{t-1}<S_0.$$

Both sides are positive. Taking logarithms and dividing by the positive number $\log k$ yields

$$t-1<\frac{\log S_0}{\log k},$$

which implies the required non-strict bound. This is the recurrence and logarithm argument in Karmarkar–Karp (FOCS 1982), p. 316, with zero-based indexing matching the trace definition.
