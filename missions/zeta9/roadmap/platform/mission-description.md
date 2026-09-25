## Motivation and history

The **Riemann zeta function** at an integer $s>1$ is the convergent series $\zeta(s)=\sum_{k=1}^{\infty}k^{-s}$. Determining whether an individual odd zeta value is rational is a central test of methods for constructing small integer linear forms in special values. Rivoal proved that infinitely many odd zeta values are irrational, a statement that does not identify any particular value beyond the separately known case $\zeta(3)$ ([Rivoal, 2000](https://arxiv.org/abs/math/0008051)). Zudilin proved that at least one of $\zeta(5),\zeta(7),\zeta(9),\zeta(11)$ is irrational ([Zudilin, 2002 preprint](https://arxiv.org/abs/math/0206176)). A September 2026 preprint claims the smaller disjunction involving $\zeta(5),\zeta(7),\zeta(9)$; it remains a preprint and still does not isolate $\zeta(9)$ ([Suman, 2026](https://arxiv.org/abs/2609.22316)). This mission asks for the single-value result itself.

## Setting

For each even integer $n\ge2$, a local $p=9$, $m=n$ construction uses polynomials $W$ of degree at most four to produce rational linear forms in $1,\zeta(3),\zeta(5),\zeta(7),\zeta(9)$. An invertible coefficient matrix $F_n$ permits a two-dimensional inverse image whose lower odd-zeta coefficients vanish. Its integer outputs therefore have the form $b+a\zeta(9)$ with $a,b\in\mathbb Z$. The five coefficient coordinates carry the weighted Euclidean norm with diagonal weights $(1,n^2,n^4,n^6,n^8)$.

The local arithmetic data include a common denominator $D_n$, Smith factors $s_{1,n}\mid s_{2,n}$, their ratio $N_n=s_{2,n}/s_{1,n}$, and $d_n=\operatorname{lcm}(1,\ldots,n)$. Set $g_n=\gcd(N_n,d_n^2)$. Let $\Delta_n$ be the weighted area of the saturated integer kernel and let $\mu_n$ be the first minimum of the associated congruence lattice $\Lambda_{g_n}$. All the quantities inside the logarithms below are positive. The analytic threshold already established in the local mathematical notes is $\tau=10.564=2641/250$; that statement has not been checked in Lean.

## Formalization targets

The goal is the single assertion

$$\zeta(9)\notin\mathbb Q.$$

The principal open mathematical subgoal is **J**: there exist $\varepsilon>0$ and infinitely many even $n\ge2$ for which $B_n+\sigma_n\le\tau-\varepsilon$, where

$$B_n=\frac{\log(D_n/s_{1,n})+\tfrac12\log\Delta_n-\tfrac12\log g_n}{n},\qquad
\sigma_n=\frac{\tfrac12\log(g_n\Delta_n)-\log\mu_n}{n}.$$

Two stronger, separately open targets are **V**, $\limsup_{n\to\infty,\,2\mid n}B_n<\tau$, and **S**, $\sigma_n\to0$ along even $n$. Together V and S imply J; they are sufficient conditions, not necessary conditions. The mathematical notes derive that J, the established analytic decay estimate, the coefficient-map identity, the Gauss bound for the second minimum, and a two-form irrationality criterion would imply the goal.

A newer independent route uses one small integer form whose coefficient polynomial has a fixed sign on the positive summation tail. The note-proved positive-kernel criterion TP shows that such a form is nonzero. The open target T asks for infinitely many even $n$ at which a first-minimum vector of the full integer-output lattice has all five Taylor coefficients at $(n+1)(2n+1)$ of one weak sign; the proved inverse-image area bound X makes those first vectors exponentially short. Another open target TG asks the same sign property for first vectors of the partial congruence lattice; TG together with V suffices because the lifted integer-output norm has exact exponent $B_n-\sigma_n$. Neither infinite sign assertion is proved, so the goal remains open.

## Significance

A proof would settle the arithmetic nature of one specified odd zeta value. It would strengthen a disjunction such as Zudilin's by identifying $\zeta(9)$ itself. The formalization would clarify two possible nonzero mechanisms: two independent small integer forms, or one small form whose sign is certified by the positive summation kernel. The local notebook has mathematical derivations for structural identities and finite certificates for $n=12,24,48,96,192$. None of those finite checks establishes the open infinite sign or asymptotic claims. Mathematical-note status and platform verification are recorded separately below.

## Difficulty

The analytic side makes individual forms small at a certified exponential rate. The two-form route still needs the second minimum of a rank-two lattice; it depends on arithmetic volume and congruence-lattice shape. The one-form route instead needs an infinite sequence of first vectors whose polynomial has a provably fixed sign on the summation tail. Five computed signs do not prove that infinite assertion. A proof that V or S fails would not settle the goal; J or the one-form route could still succeed.

## Formalization scope

The Lean goal uses Mathlib's complex `riemannZeta` at the complex number $9$ and applies `Irrational` to its real part. At this positive integer the real part equals the usual real series, so the statement does not become vacuous from an unspecified real witness. The independent-small-forms criterion and abstract volume-plus-shape margin bridge have `ACCEPTED` Lean proofs. Three additional abstract arithmetic cores, including the new exact finite prime-discount identity, are also `ACCEPTED`. Their acceptance does not establish the concrete arithmetic or infinite sign hypotheses.

The concrete arithmetic sequences and Taylor cones still require faithful Lean definitions of the coefficient matrix, saturated kernel, Smith data, weighted norm, and congruence minimum before the asymptotic targets can be posted as formal theorem items. The local mathematical DAG distinguishes **open** nodes R, J, T, TS, T5, TG, V, VA, VB, VC, VD, S from note-proved nodes F, A, G, P, TP, TA, SP, GC, FQ, FI, GO, M, C, L, LC, Q, X, Y, YD, H, Z, I. Only explicitly linked platform theorems carry platform proof status. Supporting results already present on Prove2me may be referenced, including the Zudilin four-value disjunction; it is not a proof of this goal.

## Research DAG update, 24 September 2026

The sufficient reductions include $R\leftarrow J,F,A,G,P$, $R\leftarrow T,TP,X,A,F$, $R\leftarrow TS,SP,X,A,F$, $R\leftarrow TG,TP,V,A,F$, $J\leftarrow V,S$, $V\leftarrow VA,Q,X$, $VA\leftarrow VB,Y$, $VA\leftarrow VD,YD,H,Z,Y$, and $VB\leftarrow VC,H,Z$. Each comma-separated child set is conjunctive; different sets for the same parent are alternative sufficient routes. Q is exact Smith-volume cancellation, X a uniform inverse-image area exponent bound, Y a prime-budget inequality, YD its exact discounted identity, H a translation-trace large-prime bound, and Z a sublinear small-prime bound. All the named infinite sign and asymptotic targets remain open; the arrows do not assert converses.

Q gives $B_n=[\log\Xi_n+\log(N_n/g_n)]/(2n)$, where $\Xi_n$ is the weighted area of $E_n=SF_n^{-1}$. The mathematical proof of X uses the actual varying connection $E_{n+2}W_{n+2}=E_nW_nG_n$, its exterior square, and exact rational isolation of the five roots of the limiting matrix's characteristic polynomial. It establishes

$$\limsup_{2\mid n,\,n\to\infty}\frac{\log\Xi_n}{2n}<\frac14\log(3\,711\,015\,000)\approx5.50864282.$$

Consequently VA asks for $\limsup \log(N_n/g_n)/(2n)<10.564-\frac14\log(3\,711\,015\,000)\approx5.05535718$. With $a_p=\lfloor\log_p n\rfloor$, set $\mathcal E_n=\sum_{p\le n}(v_p(N_n)-11a_p)_+\log p$ and $\mathcal H_n=\sum_{p>n}v_p(N_n)\log p$. Y proves $\log(N_n/g_n)\le9\log d_n+\mathcal E_n+\mathcal H_n$. Using $\log d_n/n\to1$, the still-open sufficient target VB is

$$\limsup_{2\mid n,\,n\to\infty}\frac{\mathcal E_n+\mathcal H_n}{n}<2(10.564)-\frac12\log(3\,711\,015\,000)-9\approx1.11071437.$$

The new local proof of H uses finite-field translation traces and the minor-gcd identity to show, for every even $n\ge8$ and prime $p>n$, that $v_p(N_n)\le\lfloor3n/(2p)\rfloor$. Thus $\mathcal H_n\le\theta(3n/2)-\theta(n)$ and $\limsup\mathcal H_n/n\le1/2$. Z gives an explicit $42\lfloor\sqrt{7n/2}\rfloor\log(7n/2)=o(n)$ upper bound for the part of $\mathcal E_n$ from $p\le\sqrt{7n/2}$. The remaining open node VC asks, with $\mathcal E_n^{\mathrm{mid}}=\sum_{\sqrt{7n/2}<p\le n}(v_p(N_n)-11)_+\log p$, for

$$\limsup_{2\mid n,\,n\to\infty}\frac{\mathcal E_n^{\mathrm{mid}}}{n}<2(10.564)-\frac12\log(3\,711\,015\,000)-9-\frac12\approx0.61071437.$$

H and Z are mathematical-note proofs, supported by finite regression checks; neither has a linked Lean theorem. The finite checks do not prove their uniform statements. A further note-proved merged-pole analysis I gives $v_p(N_n)\le38$ for $\sqrt{7n/2}<p\le n$, reducing that range's contribution to $\mathcal E_n^{\mathrm{mid}}$ from $p\le n/H_0$ to a normalized upper limit of $27/H_0$ for each fixed $H_0>1$. Its normalized trace identity involves merged pole moments rather than the original low-zeta columns, so VC remains open.

On the shape side, the new note-proved LC reformulates $\Lambda_g$ intrinsically as $\{zK_n:z(J_n/s_{1,n})\equiv0\pmod g\}$; for each prime power in $g$, one column of this integer matrix gives the local congruence condition. An abstract pair of lattices with identical Smith factors, area, and base lattice has shape defects tending respectively to $1$ and $0$, showing that the actual local slopes must be controlled. This abstract example is not a counterexample to S for the zeta construction. I and LC have no linked Lean theorem. The five archived zeta values of $n$ check definitions only and prove none of the open asymptotic nodes. The root theorem remains Open.

The exact new discount term is $\mathcal U_n=\sum_{p\le n}\min\{(11a_p-v_p(N_n))_+,9a_p\}\log p\ge0$, and YD proves $\log(N_n/g_n)=9\log d_n+\mathcal E_n+\mathcal H_n-\mathcal U_n$. The open VD target replaces VC by $\limsup(\mathcal E_n^{\mathrm{mid}}-\mathcal U_n)/n<0.61071437$ (the displayed decimal abbreviates the exact threshold above). This is weaker than VC. A separate exact local Smith certificate disproves two previously considered pointwise shortcuts: $v_{29}(N_{234})=13>12$ and $v_{257}(N_{258})=12>11$ although $257>258/2$. These finite counterexamples do not disprove VC or VD. Retaining the residue-dependent local bound and summing by the prime number theorem gives only $\limsup\mathcal E_n^{\mathrm{mid}}/n<22.4$, far above the required rate.

TP proves that a nonzero integer-output polynomial with one weak sign in its five Taylor coefficients at $u_0=(n+1)(2n+1)$ has a strictly nonzero sum. The full output lattice has a uniformly short first vector by Hermite and X, so T would close the root without V or S. For the partial lattice, if $v_n$ is a first vector of $\Lambda_{g_n}$, the exact Smith lift is $z_nE_n=(D_n/(s_{1,n}g_n))v_n$ and $\log\|z_nE_n\|/n=B_n-\sigma_n$; Hermite gives $\sigma_n\ge-O(1/n)$. Thus V and TG would close the root without S. The same note adds a global adjugate generator for the concrete congruence lattice: $\Lambda_g=\operatorname{row}_{\mathbb Z}([gI_2;\operatorname{adj}(J_n/s_{1,n})])K_n$. Five frozen partial-lattice first vectors have exact Taylor signs of one sign, but that is finite evidence only.

The conditional logarithmic cancellation, finite weighted prime-budget inequality, and exact finite prime-discount identity have separate `ACCEPTED` platform proofs; these are algebraic cores of Q, Y, and YD, not formalizations of their complete zeta-specific statements. X and TP are mathematically proved in local notes but have no faithful Lean theorems yet. S still requires a lower bound for **every** primitive congruence direction; the new T and TG routes instead need an infinite sign theorem for selected short directions.

## Taylor transfer and saddle-window update, 24 September 2026

The exact normalized Taylor connection has a rational limiting matrix $H$. Its last row has mixed signs, so one-step positive-cone preservation fails, but $H^2$ has all 25 entries strictly positive. Convergence of the actual varying connection then proves eventual strict positivity of each actual $n\to n+4$ transfer. A positive moment column and an elementary contraction argument yield the local theorem TA: every **fixed** real output $(b,a)$ with $b+a\zeta(9)\ne0$ eventually has five Taylor coefficients of the same sign as that real value. In particular both coordinate rows are eventually positive, and the minimum and maximum of their five coefficient ratios form two strictly nested mod-four interval chains converging to $\zeta(9)$. A further Perron coordinate lower bound and exterior-square upper bound prove that the logarithmic width rate is strictly below $-10.1109$ per $n$. Exact rational matrix multiplication and rational spectral intervals audit the constants. TA does not give a uniform entry time for integer outputs that change with $n$.

The local theorem SP weakens the sign condition needed for a small integer form. Let a positive window $h_n$ be fixed in advance with $h_n\to0$ and $nh_n^2/\log n\to\infty$. For a nonzero quartic, one weak sign only at the actual summation samples with $|k/n-x_*|\le h_n$, where $x_*$ is the unique positive-kernel saddle, forces the **entire** infinite weighted sum to be strictly nonzero. In particular $h_n=A_0(\log n)/\sqrt n$ works for every fixed $A_0>0$. Five central samples give a polynomial lower bound and the full outside tail is exponentially smaller. The new open target TS asks for this narrow-window sign condition along infinitely many first-minimum outputs of the full integer-output lattice. TS with SP, X, and the existing analytic decay would imply the root theorem. The frozen $n=24,192$ first polynomials have real roots on the positive half-line, yet exact integer tail bounds prove their complete weighted sums negative. These are finite signs only, not TS.

TA and SP are mathematical-note proofs, not accepted Lean theorems. The private mission milestones record TA, SP, and TS for subsequent work while the root remains Open.

## Gaussian five-point update, 25 September 2026

For the actual infinite positive kernel, the affine saddle coordinate

$$s_{n,k}=\frac{\sqrt{an}}{2x_*+1}\left(\frac{k(k+n)}{n^2}-x_*(x_*+1)\right),\qquad a=-f''(x_*)>0$$

has normalized moments of degrees zero through four converging to the standard Gaussian values $(1,0,1,0,3)$. The local proof GC controls the complete infinite tail. It implies a sharp constant-scale sign theorem: for every fixed $A>\sqrt{3/a}$, weak sign agreement at all actual samples $|k/n-x_*|\le A/\sqrt n$ forces the entire sum to be strictly same-sign for every moving nonzero real quartic. Exact rational arithmetic encloses $0.095251<\sqrt{3/a}<0.095252$. For every smaller positive $A$, moving rational quartics give strict counterexamples on the same positive kernel. These counterexamples are not asserted to lie in the actual two-dimensional integer-output space; the equality case is unproved.

The stronger operational result FQ prescribes just five actual integer samples $k_{n,j}=\lfloor nx_*+j\sqrt{n/a}+1/2\rfloor$, $j=-2,-1,0,1,2$. For all sufficiently large even $n$, the true normalized kernel moments determine **exact** five-node cubature weights that are strictly positive, independent of the moving quartic, and tend to $(1/12,1/6,1/2,1/6,1/12)$. Thus weak agreement of a nonzero quartic's five sampled signs makes its complete infinite sum strictly nonzero. This is a mathematical-note proof, not a Lean-accepted theorem.

The new open target T5 asks for infinitely many even $n$ whose full integer-output lattice has a first-minimum polynomial with these **five prescribed sampled values** of one weak sign. The proved area and analytic length bounds then make its nonzero integer form tend to zero, so $R\leftarrow T5,FQ,X,A,F$ is a checked conditional reduction. The previous TS target implies T5, because these five samples eventually lie in every fixed $A_0\log n/\sqrt n$ saddle window. No infinite sign theorem for the actual moving first vectors is yet known. Root $R$ remains Open/private. Formalization of the newly proved GC/FQ results is welcome after mathematical audit; older milestones do not gate this research line.

A separate local note GO constructs, for every sufficiently large even $n$, an **abstract** rank-two integer polynomial lattice in which every nonzero direction takes both signs already at three of the five prescribed samples. Its weighted first-minimum rate and half-area rate can both be $5$, below the established geometric upper bounds. Thus dimension, area and shortness alone cannot force T5; a proof must use the actual $E_n$ direction, connection or arithmetic structure. GO is not a counterexample to the concrete T5 statement.

The note-proved FI reformulation uses eventual positivity of the two concrete coordinate polynomials at the five samples. Their rational ratios $r_{n,j}=Q_n^A(y_{n,j})/Q_n^B(y_{n,j})$ define a strict interval $\ell_n<\zeta(9)<h_n$, contained strictly inside the Taylor coefficient ratio interval. Its width inherits logarithmic exponential rate below $-10.1109$. For a nonzero integer output $(b,a)$ with $a\ne0$, weak five-sample sign agreement is **equivalent** to $-b/a\notin(\ell_n,h_n)$; endpoints are allowed because zeros are allowed. This makes T5 a precise open question about the changing first output's rational slope. FI does not establish that slope avoidance infinitely often.

On the arithmetic route, a 25 September exact periodic-envelope calculation sharpens the earlier $22.4$ coarse bound to $\limsup(\mathcal E_n^{\mathrm{mid}}-\mathcal U_n)/n<22.337$. The required VD threshold remains about $0.61071437$. The calculation provides no positive linear lower bound for the discount and does not close VD.

## First-output arithmetic and critical-margin update, 25 September 2026

The local proof FO gives a uniform theorem for **every** shortest output of the actual full lattice. If $A=\lambda_1>0$ and $B=|\lambda_2|$ are the top two limiting connection eigenvalue moduli and $\delta=\frac14\log(A/B)>5.05545$, then for every $0<\varepsilon<\delta$, all sufficiently large even $n$ and all first outputs $(b,a)$ satisfy $a\ne0$ and $|b+a\zeta(9)|\le e^{-(\delta-\varepsilon)n}$. Under the unproved rationality hypothesis $\zeta(9)=c/d$, all late first outputs would consequently equal $\pm(-c,d)$, whose slopes lie **inside** the five-sample open interval. Thus uniform approximation does not settle the open five-sample sign target T5.

The note-proved FC formula makes each five-sample rational endpoint denominator exact. With $A_n=d_n^9F_n$, $C_n=S\operatorname{adj}(A_n)$ and mixed fourth-minor gcd $\delta_{4,n}^*$, write $\widetilde C_n=C_n/\delta_{4,n}^*$. At an actual sample $t=k(k+n)$, the reduced denominator of $r_j$ is $|\widetilde C_Bv(t)|/\gcd(|\widetilde C_Bv(t)|,|\widetilde C_Av(t)|)$. If $\ell_n=P_-/Q_-$, $h_n=P_+/Q_+$ and an integer slope $-b/a$ lies strictly inside their interval, then $|a|(h_n-\ell_n)>1/\min(Q_-,Q_+)$. Every first output has $|a|\le\lambda_{1,n}\|E_{B,n}W_n\|/\Xi_n$. Hence the new **open** sufficient target FD asks for infinitely many eligible even $n$ with

$$\frac{\lambda_{1,n}\|E_{B,n}W_n\|}{\Xi_n}(h_n-\ell_n)\min(Q_-,Q_+)\le1.$$

FD and FC together imply T5. The missing uniform estimate is the evaluation gcd/denominator and first-output height product; the existing exponentially narrow interval does not control it. The proved XL result gives a real lower bound $\liminf\log\Xi_n/(2n)\ge\frac14\log(A|\lambda_5|)>\frac14\log(1499/10)$ and first-output height upper exponent $\frac14\log(A/|\lambda_5|)$. Reaching the sharper height exponent $\delta$ requires the actual zero-value row to have second-mode lower growth; a finite frozen spectral projection does not prove that. A rational alternative connection FM preserves the limiting spectrum, eventual two-step positivity, five actual sample nodes, and exact positive cubature while its first outputs fail T5 eventually. It is not a counterexample to the actual finite-parameter connection.

The new note-proved CM criterion identifies a separate **open** critical target CP. The actual kernel mass satisfies $Z_n\sim C_Zn^{-5}e^{f_*n}$. Put $T_n=n^5e^{-f_*n}$. Positive Taylor moments make both fixed output rows $\Theta(T_n)$, and the inverse-area bound makes their normalized difference rank one. The resulting exact equivalence is

$$\zeta(9)\notin\mathbb Q\quad\Longleftrightarrow\quad\lambda_{2,n}=o(T_n)\quad\Longleftrightarrow\quad\liminf_{2\mid n,\,n\to\infty}\lambda_{2,n}Z_n=0.$$

CP asks only for the last limit inferior. If $\zeta(9)=c/d$, its left side has a positive lower bound $1/(d C_Z\|v_*\|)$ after division by $T_n$. Under that same conditional hypothesis, the primitive zero relation $\pm(-c,d)$ is eventually the only first direction, $\lambda_{1,n}\lambda_{2,n}/\Xi_n\to1$, and $\lambda_{1,n}/(\Xi_nZ_n)$ stays within positive constant bounds. Equivalently, proving $\lambda_{1,n}/(\Xi_nZ_n)\to\infty$ would settle the root. CM proves this equivalence, **not** CP or irrationality. The local DAG now records $R\leftarrow CP,CM$ and $T5\leftarrow FD,FC$ as alternative sufficient reductions. No older milestone formalization is required before new mathematics proceeds. Root $R$ remains Open/private.

## Selected references

- T. Rivoal, *La fonction Zêta de Riemann prend une infinité de valeurs irrationnelles aux entiers impairs*, 2000, [arXiv:math/0008051](https://arxiv.org/abs/math/0008051).
- W. Zudilin, *Arithmetic of linear forms involving odd zeta values*, 2002, [arXiv:math/0206176](https://arxiv.org/abs/math/0206176); see also the 2001 four-value theorem cited there.
- S. Suman, *At least one of the three numbers $\zeta(5)$, $\zeta(7)$, $\zeta(9)$ is irrational*, preprint, 2026, [arXiv:2609.22316](https://arxiv.org/abs/2609.22316).

## Platform DAG wiring update, 25 September 2026

The goal theorem now carries machine-checked decompositions instead of standing as a
bare open leaf. Two independent reductions of the goal were accepted as
proof-sketches, and five new private theorem items were published.

The goal's **one-form** decomposition imports
`ZetaNine.irrational_of_small_nonzero_integer_forms` (Proved) and
`ZetaNine.exponentially_small_nonzero_forms_of_zeta_nine` (Open). The criterion states
that a real number admitting nonzero integer forms of arbitrarily small absolute
value is irrational; the open child asks for a fixed $c>0$ with nonzero forms
$b+a\,\zeta(9)$ of absolute value below $e^{-cn}$ for all sufficiently large $n$.
The goal's **two-form** decomposition imports
`ZetaNine.irrational_of_two_small_integer_forms` (Proved, the mission's existing
criterion) and `ZetaNine.exponentially_small_independent_forms_of_zeta_nine` (Open),
which additionally requires the two coefficient vectors to be non-proportional.

Both open children are strictly stronger than the goal and are **not** equivalent to
it: they demand approximations of a fixed exponential quality, which a general
irrational number need not admit. They are the definition-free packaging of the
local notes' combination of the open exponential margin J, the coefficient map F,
the analytic decay A and the Gauss lattice bound G, and proving either one settles
the goal. The Lean content of these two reductions is a short final assembly; the
mathematical work lives entirely in the open child, and neither child is claimed
proved. The one-form child carries an explicit nonvanishing clause; the two-form
child does not need one, because with two non-proportional coefficient vectors at
most one form can vanish.

Three further items are proved and fully general, and form the formalisable core of
local nodes TP and FQ. `ZetaNine.irrational_of_small_nonzero_integer_forms` is the
criterion half of TP. `ZetaNine.taylor_sign_implies_kernel_sum_pos` is the
positive-kernel half of TP: for a strictly positive kernel $R$, sampling map $u$,
polynomial $p$ and expansion point $u_0$, if every sample satisfies $u(k)\ge u_0$,
every Taylor coefficient of $p$ at $u_0$ is nonnegative, the weighted series is
summable, and $p$ is positive at one sample, then the complete weighted sum is
strictly positive. `ZetaNine.quadrature_exact_of_moments` is the exact algebraic core
of FQ: agreement of a linear functional with a five-node rule on the moments of
degrees zero through four forces agreement on every polynomial of degree at most
four. None of the three mentions the concrete construction, and none of them
asserts positivity of the actual cubature weights or any infinite sign condition.

**What is deliberately not wired.** The concrete construction still has no Lean
definitions: there is no formal coefficient matrix $F_n$, saturated kernel, Smith
data, weighted area or congruence-lattice minimum. Consequently the local reductions
$V\leftarrow VA,Q,X$, $VA\leftarrow VB,Y$, $VA\leftarrow VD,YD,H,Z,Y$,
$VB\leftarrow VC,H,Z$, $T5\leftarrow FD,FC$ and $J\leftarrow V,S$ are **not** posted
as platform decompositions, and the milestones for X, VB, VC, VD, S, J, T, TG, TS,
T5, FD, FM and CP remain unlinked to theorem items. Two reasons, recorded so that
nobody re-derives them: a child of the goal stated only as "small integer forms
exist" is *equivalent* to the goal once a criterion is available, so it would be a
disguised restatement rather than a decomposition; and a reduction whose parent has
free parameters cannot import closed child theorems, so a genuine multi-level graph
over the concrete nodes needs the definition layer first. The arrow arguments
themselves are elementary once the objects exist. Until then the platform dependency
graph should be read as one open analytic obligation per route plus three proved
general lemmas, with the remaining milestones still at research-notebook status.

All five new statements were read back blind by an independent auditor before
publication. The goal theorem remains **Open**.
