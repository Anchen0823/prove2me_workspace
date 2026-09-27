# Zudilin's theorem: at least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational — proof sketch

**Target (Prove2Me mission `FCP.Zeta.zudilin_five_seven_nine_eleven`):**

$$\exists\, a \in \{5,7,9,11\} \text{ such that } \zeta(a) \text{ is irrational}.$$

**Theorem (W. Zudilin, 2001).** At least one of the four numbers ζ(5), ζ(7), ζ(9), ζ(11)
is irrational. This is the sharpest known irrationality localisation among small odd
zeta values: ζ(3) is irrational (Apéry 1978), Rivoal (2000) proved that infinitely many
odd zeta values are irrational and Ball–Rivoal (2001) gave quantitative versions, and
Zudilin's note closes the window {5, 7, 9, 11}. The irrationality of ζ(5) itself remains
open; a 2026 preprint claims a strengthening to "one of ζ(5), ζ(7), ζ(9)" (arXiv:2609.22316,
not verified here).

---

## 0. Status of this submission

This document is a **proof sketch** submitted to Prove2Me as a *reduction* of the mission
goal to four frontier children in the `ZudilinZeta` namespace. On the platform
(2026-09-25):

| Node | Status |
| --- | --- |
| `FCP.Zeta.zudilin_five_seven_nine_eleven` (mission goal) | **Open — first decomposition accepted (SKETCH_ACCEPTED)** |
| `ZudilinZeta.zetaR_eq_riemannZeta` (bridge, created here) | **Proved** (full formal proof, verified) |
| `ZudilinZeta.exists_saddle_root_params13` (created here) | Open |
| `ZudilinZeta.zudilin_numeric_C0_gt_C1` (pre-existing) | Open |
| `ZudilinZeta.zudilin_lemma3` (pre-existing) | Open |

The mission is closed as soon as the three open children are proved; the reduction
guarantees the goal follows.

## 1. The linear forms (Lemma 1 of the note; construction)

Let $r = 3$, $q = 13$ and take the parameters

$$\eta_0 = 91,\quad \eta_1=\eta_2=\eta_3 = 27,\quad \eta_4=29,\ \eta_5=30,\ \dots,\ \eta_{13}=38,$$

which satisfy $\eta_1\le\dots\le\eta_{13}=38 < 91/2 = 45.5$ and
$\eta_1+\dots+\eta_{13}=416\le 91\cdot(13-3)/2 = 455$ (condition (1) of the note).

For $n>0$ put $h_0=\eta_0 n+2$, $h_j=\eta_j n+1$ ($1\le j\le 13$) and define the
rational function

$$R_n(t)=(h_0+2t)\prod_{j=1}^{3}\frac{\Gamma(h_j+t)}{(h_j-1)!\,\Gamma(1+t)}\cdot
\frac{\Gamma(h_0+t)}{(h_j-1)!\,\Gamma(1+h_0-h_j+t)}
\prod_{j=4}^{13}(h_0-2h_j)!\,\frac{\Gamma(h_j+t)}{\Gamma(1+h_0-h_j+t)}.$$

Since $R_n(t)=O(t^{-2})$, the series $F_n=\frac{1}{2!}\sum_{t\ge0}R_n^{(2)}(t)$ converges.
Expanding $R_n$ in partial fractions and summing over $t$ rewrites $F_n$ as a rational
linear combination of $1$ and the odd zeta values $\zeta(5),\zeta(7),\zeta(9),\zeta(11)$
(the intermediate and even terms cancel by the choice of parameters) — **Lemma 1** of [Z1].

## 2. Integrality and the denominator (Lemma 1, (3); arithmetic layer)

With $D_N=\operatorname{lcm}(1,\dots,N)$ and the functions $m_j,\varphi,\Phi_n$ defined as in
the note, Lemma 1 asserts the arithmetic form

$$\Lambda_n := D^3_{m_1 n}D_{m_2 n}\cdots D_{m_{10} n}\cdot \Phi_n^{-1}\cdot F_n
\in \mathbb{Z} + \mathbb{Z}\zeta(5) + \mathbb{Z}\zeta(7) + \mathbb{Z}\zeta(9) + \mathbb{Z}\zeta(11).$$

Growth rates: $\log D_{m_j n}/n\to m_j$ (prime number theorem), and $\log \Phi_n/n\to\varpi$
where $\varpi=\int_0^1\varphi\,d\psi-\int_0^{1/m_{10}}\varphi(x)x^{-2}dx$ is evaluated by the
Chudnovsky–Rukhadze–Hata method. Hence the denominators grow at most like $e^{C_1 n+o(n)}$
with

$$C_1 = 3m_1+m_2+\dots+m_{10}-\varpi = 226.24944266\ldots$$

(the arithmetic content of the note; recorded in `zudilin_numeric_C0_gt_C1`).

## 3. The asymptotic decay (Lemma 2; saddle point)

Let $\tau_0$ be the saddle point: a root of

$$(\tau-\eta_0)^3(\tau-\eta_1)\cdots(\tau-\eta_{13})
= \tau^3(\tau-\eta_0+\eta_1)\cdots(\tau-\eta_0+\eta_{13})$$

in the upper half-plane of maximal real part, with $\operatorname{Re}\tau_0<\eta_0$ and
$\operatorname{Im} f_0(\tau_0)\notin\pi\mathbb{Z}$, $f_0$ the auxiliary function of the note.
The complex-integral representation of $F_n$ (residues on a line $\operatorname{Re}t=\text{const}$)
and Stirling's formula give, by the saddle-point method,

$$\limsup_{n\to\infty}\frac{\log|F_n|}{n}=\operatorname{Re}f_0(\tau_0)=-C_0,\qquad
C_0=227.58019641\ldots$$

The condition $\operatorname{Im}f_0(\tau_0)\notin\pi\mathbb{Z}$ keeps the leading asymptotic
coefficient nonzero, so $F_n\neq 0$ (hence $\Lambda_n\neq 0$) for all large $n$.
The existence of such $\tau_0$ for the parameters above is the node
`exists_saddle_root_params13`; the values of $C_0,C_1$ are the node
`zudilin_numeric_C0_gt_C1` (read as $227.58019641\le C_0<227.58019642$,
$226.24944266\le C_1<226.24944267$).

## 4. The diophantine criterion (Lemma 3; elementary)

Since $C_1<C_0$ (margin $C_0-C_1\approx 1.3308$), we get $|\Lambda_n|\le e^{(C_1-C_0+o(1))n}\to0$,
with $\Lambda_n\neq0$ an integer-coefficient linear form in $1,\zeta(5),\zeta(7),\zeta(9),\zeta(11)$.

**Criterion (Nesterenko-type; self-contained).** If all four zeta values were rational with
common denominator $Q$, then $\Lambda_n\in(1/Q)\mathbb{Z}$, so $\Lambda_n\ne 0$ would force
$|\Lambda_n|\ge 1/Q$, contradicting $|\Lambda_n|\to0$. Hence at least one of
$\zeta(5),\zeta(7),\zeta(9),\zeta(11)$ is irrational. ∎

This is **Lemma 3** of the note, instantiated at $r=3$, $q=13$: it outputs
$k\in\{1,2,3,4\}$ with $\operatorname{zetaR}(3+2k)$ irrational.

## 5. Bridging to Mathlib's `riemannZeta` (done)

The goal is stated with Mathlib's complex `riemannZeta`, while the linear-form layer uses
the elementary series $\operatorname{zetaR} k=\sum_{n\ge0}(n+1)^{-k}$. For $k\ge2$ the two
agree (Mathlib's `zeta_eq_tsum_one_div_nat_add_one_cpow` + `Complex.cpow_natCast` +
`Complex.ofReal_tsum`); this is the node `ZudilinZeta.zetaR_eq_riemannZeta`, **formally
proved and accepted**. Transferring irrationality along this identification and using
$3+2k\in\{5,7,9,11\}$ for $k\in\{1,2,3,4\}$ closes the goal.

## 6. What a verifier must check (open children)

1. **`exists_saddle_root_params13`** — existence of $\tau_0$ (root of the degree-13
   saddle polynomial in the upper half-plane, maximal real part, $\operatorname{Re}\tau_0<91$,
   $\operatorname{Im}f_0(\tau_0)\notin\pi\mathbb{Z}$). Numerics: $C_0=-\operatorname{Re}f_0(\tau_0)$
   matches $227.58019641\ldots$; a rigorous proof needs a sign/IVT argument on the polynomial
   plus interval arithmetic for the inequalities.
2. **`zudilin_numeric_C0_gt_C1`** — rigorous bounds for $C_0$ and $C_1$ at these parameters
   (high-precision evaluation with error control).
3. **`zudilin_lemma3`** — the elementary criterion of §4 combined with the asymptotic and
   arithmetic lemmas ($|\Lambda_n|=e^{(C_1-C_0+o(1))n}$, $\Lambda_n\ne0$).

## References

[Z1] W. V. Zudilin, *One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational*,
Uspekhi Mat. Nauk 56:4 (2001), 149–150; English transl. Russian Math. Surveys 56:4
(2001), 774–776, https://doi.org/10.4213/rm427 .

[Z2] W. V. Zudilin, *Irrationality of values of the Riemann zeta function*,
Izv. Math. 66:3 (2002), 489–542 (full proofs of the arithmetic lemmas).

[R] T. Rivoal, *La fonction zêta de Riemann prend une infinité de valeurs irrationnelles
aux entiers impairs*, C. R. Acad. Sci. Paris Sér. I Math. 331 (2000), 267–270.

[BR] K. Ball, T. Rivoal, *Irrationalité d'une infinité de valeurs de la fonction zêta aux
entiers impairs*, Invent. Math. 146 (2001), 193–207.

[A] R. Apéry, *Irrationalité de ζ(2) et ζ(3)*, Astérisque 61 (1979), 11–13.
