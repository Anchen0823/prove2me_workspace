## Correction: the leading coefficient of the Ehrhart polynomial is not the volume

The milestone for the $H_4$ rung previously read

> its leading coefficient $11/11340$ is the volume of $B_4$ and its normalised volume is $352$

The first half of that sentence is wrong, by a factor of $n^{n-1} = 64$ at $n = 4$. What
Beck-Pixton (*The Ehrhart polynomial of the Birkhoff polytope*, Discrete Comput. Geom. **30**
(2003) 623-637, [arXiv:math/0202267](https://arxiv.org/abs/math/0202267), sections 3 and 4)
actually give is

| quantity | value | relation |
|---|---|---|
| leading coefficient of $H_4(t)$ | $11/11340$ | as originally stated |
| Euclidean volume $\operatorname{vol}(B_4)$ | $176/2835$ | $= 4^{3}\cdot 11/11340 = n^{n-1}\times$ (leading coefficient) |
| lattice-normalised volume | $352$ | $= 9!\cdot 11/11340$ |

The factor is the relative fundamental volume of the counting lattice, $n^{n-1}$. The leading
coefficient of the Ehrhart polynomial is the *lattice-normalised* volume divided by $d!$, not the
Euclidean volume. For comparison, $\operatorname{vol}(B_3) = 9/8$, while the leading coefficient
of $H_3(t)$ is $1/8$.

The milestone text has been corrected accordingly. **The formal statement of the rung is
unaffected**: `MagicSquares.semi_magic_count_four` is the cleared-denominator integer identity
$11340\cdot H_4(t) = 11t^{9}+198t^{8}+\cdots+11340$, which is term-for-term the polynomial in
Beck-Pixton section 3, and which was independently re-derived here from direct enumeration on
$t = 0,\dots,16$ (fitted on the first ten values, checked on all seventeen).
