Let $S$ be a finite index set. For each $i\in S$, let $v_i,a_i$ be nonnegative integers and let $w_i\ge0$ be a real weight. Then

$$
\sum_{i\in S}(v_i-2a_i)_+w_i
\le9\sum_{i\in S}a_iw_i
+\sum_{i\in S}(v_i-11a_i)_+w_i.
$$

Here $(r)_+=\max(r,0)$; Lean's subtraction on natural numbers is truncated at zero. Pointwise, if $v_i\le11a_i$, then $(v_i-2a_i)_+\le9a_i$. If $v_i>11a_i$, both positive parts are ordinary differences and equality holds:

$$
v_i-2a_i=9a_i+(v_i-11a_i).
$$

Multiplying by $w_i\ge0$ and summing proves the theorem. Taking $i$ to range over primes $p\le n$, $v_i=v_p(N_n)$, $a_i=v_p(d_n)$, and $w_i=\log p$ gives the small-prime part of the new $\zeta(9)$ arithmetic budget. The separate contribution of primes $p>n$ and the prime number theorem are outside this formal statement.
