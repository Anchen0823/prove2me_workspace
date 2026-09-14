# Remaining finite evaluation

The limit passages have separate complete Lean proofs. The unproved step is the exact finite identity, not an irrationality assumption.

Write $c_i=(-1)^i\binom ni$. Expanding the numerator after the finite geometric truncation reduces the integral to

$$\sum_{i,j=0}^n c_i c_j\sum_{v=0}^{N-1}J(n+i+v,n+j+v),$$

where the elementary logarithmic moment is

$$J(a,b)=\int_0^1\int_0^1\frac{x^ay^b}{-\log(xy)}\,dy\,dx
=\begin{cases}1/(a+1),&a=b,\\
\log((b+1)/(a+1))/(b-a),&a\ne b.\end{cases}$$

For the present application $a,b\ge1$. One source-faithful proof inserts $-1/\log(xy)=\int_0^\infty(xy)^t\,dt$, justifies integration order, and integrates the resulting rational function of $t$.

The diagonal sum becomes $\sum_i\binom ni^2(H_{N+n+i}-H_{n+i})$. Pairing off-diagonal indices gives

$$2\sum_{i<j}\frac{c_i c_j}{j-i}\sum_{k=1}^{j-i}
\log\frac{N+n+i+k}{n+i+k}.$$

Now use the binomial-square sum and the square of $\sum_i c_i=0$ to extract $\binom{2n}{n}(H_N-\log N)$. The constant logarithmic term is Sondow's equation (11). Identifying it with the positive-coefficient form defining $L_n$ requires Lemma 2 / the Appendix identity. The remaining shifts are exactly `cutoffError n N`.

Reference: [Sondow v2](https://arxiv.org/pdf/math/0209070), Theorem 1, equations (9)-(11), Lemma 2 and Appendix.

`check_cutoff_coefficients.py` independently compares the expanded moment formula and the proposed finite evaluation as exact rational coefficients of prime logarithms for all $1\le n,N\le8$. All 64 checks pass. This is an indexing/sign audit only; it does not prove the integral formula or the infinite family of combinatorial identities.
