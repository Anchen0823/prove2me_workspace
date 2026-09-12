For every coefficient family satisfying $|c_d|\le1$ on the positive odd
integers $d\le UV$, we prove

$$
T_I\le\frac{96}{\pi^2}\frac{x}{(x/q)^2}\log(4x)
\log\left(\frac{4eq}{\pi}\right).
$$

The proof works directly with the compactly supported odd-lattice
amplitudes, so no mollification or smoothness assumption is needed.
The parameter assumptions imply $x\ge6400$ and $q\ge1602$.

For a fixed divisor index, let

$$
F_d(n)=(\log(2n+1)+c_d\log d)\eta_0(d(2n+1)/x).
$$

The zero extension makes this a finitely supported function on the
integers. Two discrete summations by parts bound its Fourier sum by the
sum of the moduli of its second differences, divided by the square of
the Fourier multiplier. The multiplier on the odd lattice has modulus
$2|\sin(2\pi d\alpha)|$.

We establish the second-difference estimate from the actual piecewise
derivative of the log-weighted cutoff. Its bounded variation includes the
two endpoints and the middle corner of the cutoff. Integrating the
derivative increments over intervals of length two yields

$$
\sum_n|F_d(n+2)-2F_d(n+1)+F_d(n)|
\le96\frac{d}{x}\log(4x).
$$

The unit-numerator phase hypotheses then give the finite trigonometric
estimate

$$
\sum_{\substack{d\le UV\\d\ \mathrm{odd}}}
\frac{d}{\sin^2(2\pi d\alpha)}
\le\frac4{\pi^2}q^2\log\left(\frac{4eq}{\pi}\right).
$$

Both signs of the numerator are handled. The estimate is proved using
the actual phase window, a Taylor bound for sine, and an odd harmonic-sum
bound; it does not rely on the reversed intermediate sine comparison in
the source text. Combining these estimates and rewriting $q^2/x$ as
$x/(x/q)^2$ proves the claim.

All variation, support, discrete Fourier, and trigonometric arguments are
included in the proof file. It imports no Open theorem and assumes no
Fourier decay or variation bound. The Vaughan decomposition and the Type II
estimate are separate children of the parent reduction.
