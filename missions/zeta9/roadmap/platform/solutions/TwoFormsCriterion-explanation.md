For every real number $x$, suppose that arbitrarily small positive $\varepsilon$ admit two integer pairs $(b_1,a_1)$ and $(b_2,a_2)$ with nonzero determinant and

$$
|b_i+a_i x|<\varepsilon\qquad(i=1,2).
$$

Then $x$ is irrational. The key point is that a sufficiently small rational linear form with integer coefficients must vanish exactly.

Assume instead that $x=a/b$ for integers $a,b$ with $b\ne0$. Choose $\varepsilon=1/|b|$. For either pair $(c,d)$ supplied by the hypothesis,

$$
\left|c+d\frac ab\right|=\frac{|cb+da|}{|b|}<\frac1{|b|}.
$$

The integer $cb+da$ therefore has absolute value less than $1$, so it is zero. Applying this to both pairs gives $b_1b+a_1a=0$ and $b_2b+a_2a=0$. Eliminating $a$ yields

$$
(b_1a_2-b_2a_1)b=0.
$$

Since $b\ne0$, this contradicts the nonzero determinant. Thus no rational representation of $x$ exists.
