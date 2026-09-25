# Analytic foundations for a ζ(7) Hankel attempt

Status (2026-09-24): the lemmas below are proved for the stated construction, but **they do not prove that ζ(7) is irrational**. In particular, positivity and degree do not supply the required integral normalization or a negative final exponent. I independently checked the analytic steps against §§2 and 6 of `referpaper/ZETA5_IS_IRRATIONAL.pdf` (text extraction in `tmp/pdfs/zeta5-reading/paper.txt`). The paper's specific potential certificate is for `q=3, α=3/40` and is not independently certified here.

## 1. A positive functional for every odd `s >= 3`

Write `s=2r+1`, `m=s-1=2r`, and set

```
w_s(y) = [2(2π)^m/m!] y^(m+1) sum_{ell>=1} ell^m exp(-2π ell y),  y>0.
```

Every term is positive. The standard expansion of `1/(exp(2πy)-1)` at zero gives `w_s(y) -> 1/π` as `y ↓ 0`; direct comparison of the series gives `w_s(y) <= C_s(1+y)^s exp(-2πy)` for `y >= 1`. Thus all polynomial moments exist. Tonelli and the gamma integral give, for `e >= 0`,

```
∫_0^∞ y^(2e) w_s(y) dy
 = 2(2e+s)! / [m!(2π)^(2e+2)] ζ(2e+2)
 = (-1)^e B_(2e+2) (2e+s)! / [m!(2e+2)!].             (1)
```

The last equality is Euler's even-zeta formula with `B_1=-1/2`. In particular, `μ_7(1)=7/12`.

For `a>0`, let `f(y)=1/(exp(2πy)-1)` and `g_a(y)=y^(m+1)/(y²+a²)`. Since `w_s(y)=2y^(m+1)f^(m)(y)/m!` and `m` is even, integration by parts `m` times gives

```
∫_0^∞ w_s(y)/(y²+a²) dy = (2/m!) ∫_0^∞ f(y) g_a^(m)(y) dy.
```

At zero, `g_a^(k)(y)=O(y^(m+1-k))` for `0<=k<m`, while `f^(j)(y)=O(y^(-j-1))`; each boundary product is `O(y)`. At infinity all such products vanish exponentially. Polynomial division of `g_a`, followed by differentiating its remaining `y/(y²+a²)` term, gives the useful exact identity

```
g_a^(m)(y) = m! a^m Im (a-iy)^(-s).                    (2)
```

Hermite's integral formula (valid for `a>0`, `s>1`) then gives

```
∫_0^∞ w_s(y)/(y²+a²) dy
 = a^m ζ(s,a) - 1/(s-1) - 1/(2a).                       (3)
```

For integer `j>=1`, `ζ(s,j)=ζ(s)-H_(j-1)^(s)` and `H_j^(s)=H_(j-1)^(s)+j^(-s)`, so (3) becomes

```
μ_X(1/(t+j²)) = j^(s-1)(X-H_j^(s)) - 1/(s-1) + 1/(2j)  (X=ζ(s)). (4)
```

**Sign check:** the `+1/(2j)` in (4) is correct only with `H_j`, because (3) has `-1/(2j)` with the Hurwitz value `ζ(s,j)`. Defining `μ_X` by (1) on monomials and (4) on simple poles, polynomial division makes it a well-defined `Q`-linear map on rational functions having only simple poles at `-j²`; every output is affine in `X` with rational coefficients. Equations (1)--(3) prove the integral identity `μ_(ζ(s))(R)=∫_0^∞R(y²)w_s(y)dy` on that domain.

## 2. Matrix positivity and exact degree

Fix integers `0<=N<K`, `q>=1`, put `h=K-N`, and write `D_a(t)=∏_(j=1)^a(t+j²)` and `D_tail=D_K/D_N`. Define

```
G_ij(X) = μ_X(D_N(t)^(2q) t^(i+j)/D_K(t)),  0<=i,j<h,
Δ_K(X)=det G(X).
```

At `X=ζ(s)`, for every nonzero real polynomial `P(t)=∑_(i<h)c_i t^i`,

```
c^T G(ζ(s)) c
 = ∫_0^∞ [D_N(y²)^(2q)/D_K(y²)] P(y²)² w_s(y)dy > 0.
```

The ratio and weight are strictly positive on `y>0`; a nonzero polynomial cannot vanish there identically. Thus `G(ζ(s))` is positive definite and `Δ_K(ζ(s))>0`.

After cancellation the rational function is `D_N^(2q-1)t^(i+j)/D_tail`. Its residue at `t=-j²` (`N<j<=K`) is

```
(-j²)^(i+j) D_N(-j²)^(2q-1)/D_tail'(-j²).
```

Only the simple-pole part contributes to the `X` coefficient; polynomial quotients are independent of `X`. With `V_(i,j)=(-j²)^i` and

```
c_j = j^(s-1) D_N(-j²)^(2q-1)/D_tail'(-j²),
```

we obtain `[X]G=V diag(c_j) V^T`. The `h` nodes `-j²` are distinct, and every `c_j` is nonzero, hence

```
[X^h]Δ_K(X) = (det V)^2 ∏_(j=N+1)^K c_j != 0.        (5)
```

Therefore `Δ_K∈Q[X]` has **degree exactly `h`**, for any odd `s>=3` and any `q>=1`. This proves nonvanishing of the polynomial without a numerical determinant calculation.

The restriction `h=K-N` is convenient for the source paper's arithmetic basis, but is **not** needed for positivity. If instead the matrix size is an independent integer `H>K-N`, put `r=K-N`, and use the monic integral basis

```
1,t,...,t^(r-1), D_tail, t D_tail,...,t^(H-r-1)D_tail.
```

Its change-of-basis determinant is `1`. Every entry with at least one vector from the second block is a polynomial moment, because that vector cancels `D_tail`; it is independent of `X`. The `X` coefficient of the first `r×r` block is the invertible `V_r diag(c_j)V_r^T` from (5). The bottom-right block `C` is also independent of `X` and is positive definite: at `X=ζ(s)` it is a principal submatrix of the positive Gram matrix in this basis. Expanding the determinant in its top `r` rows/columns gives

```
[X^r] det G_H(X) = det(V_r diag(c_j)V_r^T) det C != 0.
```

Thus `deg det G_H = r` for **every `H>=r`**, while `det G_H(ζ(s))>0`. Equivalently one may take the Schur complement of `C` and obtain an `r×r` affine matrix. This rules out an algebraic vanishing obstruction to enlarging the Hankel size. It does not show that the enlarged determinant has a cheap integer normalization: `C^(-1)` in the Schur complement can introduce substantial denominators, and the prime-by-prime estimates must be redone for independent `H`.

## 3. External field and the real asymptotic bound

Assume `α=N/K` and `λ=h/K=1-α` remain fixed as `K` grows (taking `K` through a suitable arithmetic progression). Under `y=K√t`, the external field is

```
V_(q,α)(t) = 2π√t + ∫_0^1 log(t+u²)du
                        - 2q∫_0^α log(t+u²)du,  t>=0. (6)
```

For `t>0`, let `I_a(t)=a log(t+a²)-2a+2√t arctan(a/√t)`; then `V=2π√t+I_1-2q I_α`. The limit at zero is finite. The coefficient `2q` is dictated by the numerator `D_N^(2q)`; the zeta index `s` changes only lower-order factors of the weight and does **not** change this field.

Here is a precise conditional form of the real bound. Suppose a positive measure `ρ` of mass `λ`, supported in a fixed compact subset of `(0,∞)`, has finite logarithmic energy `I(ρ)=∬log|t-u|dρ(t)dρ(u)` and satisfies

```
2 U_ρ(t) - V_(q,α)(t) <= M      for all t>=0,       (7)
U_ρ(t)=∫log|t-u|dρ(u).
```

Assume in addition a local mass estimate sufficient to make the circle regularization error `O(√ε)` uniformly in its center; any fixed finite positive sum of arcsine measures on nondegenerate intervals has this property. Then the zero-mass logarithmic-energy inequality, applied to circles of radius `ε=K^(-2)` around an arbitrary configuration `t_1,...,t_h`, gives

```
2∑_(i<j)log|t_i-t_j| - K∑_i V_(q,α)(t_i)
 <= [λ M-I(ρ)]K² + O_(ρ,q,α)(K log K).             (8)
```

For completeness, use `σ=K^(-1)∑ω_(t_i,ε)` and `I(σ-ρ)<=0`. Mutual circle energies are at least `log|t_i-t_j|`; each self-energy is `log ε`, while replacing a circle-averaged `U_ρ` by its center costs `O(√ε)`. The resulting error is `-h log ε+O(hK√ε)=O(K log K)`. On the unbounded integration domain, apply (8) with `V` replaced by `V-√t/K`; (7) then changes by only `O(1/K)` uniformly, because `V(t)-2U_ρ(t)` grows as `2π√t+O(log t)` at infinity. This retains an integrable `exp(-√t)` factor.

The elementary right-endpoint Riemann estimate is, uniformly for `t>=0` and `0<=m<=K`,

```
0 <= ∑_(j=1)^m log(t+(j/K)²)
       -K∫_0^(m/K)log(t+u²)du <= 2 log K + O(1).   (9)
```

The upper error is largest at `t=0`, where it follows from `log(m!)`; its derivative in `t` is nonpositive. Andréief's identity, (9), the weight bound, and (8) give

```
log Δ_K(ζ(s))
 <= 2λ(λ+2qα-1) K² log K
    + [λ M-I(ρ)]K² + O_(s,q,α,ρ)(K log K).         (10)
```

The leading `log K` coefficient can be checked directly: the squared Vandermonde contributes `2h(h-1)log K`; the `D` ratio contributes `2h(2qN-K)log K`; the fixed-`s` weight, Jacobian, Riemann errors, and `h!` contribute only `O(K log K)`.

For comparison with the ζ(5) paper, introduce the *candidate* factorial normalization

```
S_(K,N,q) = 4^(h-1) (K!)^(2h) /
             [(N!)^(4qh) ∏_(i=1)^(h-1)((2i)!)²]  >0.
```

Stirling summation yields

```
log S_(K,N,q)
 = -2λ(λ+2qα-1) K² log K + C*(q,α)K² + O_(q,α)(K log K),
C*(q,α)=-2λ+4qαλ(1-log α)+3λ²-2λ²log(2λ).       (11)
```

For `α=0`, interpret `α log α=0` and `0!=1`. Hence the **real** bound is

```
log[S_(K,N,q)Δ_K(ζ(s))]
 <= [λ M-I(ρ)+C*(q,α)]K² + O_(s,q,α,ρ)(K log K). (12)
```

For `q=3, α=3/40, λ=37/40`, the external field, comparison measure, `M=-1329/200`, and claimed `λM-I(ρ)+C*<-1.36699` in the supplied ζ(5) paper are formally the same for `s=7`. The `s` dependence is confined to the `O_s(K log K)` term. **This transfers only the real-value estimate if the paper's explicit potential certificate is accepted; it says nothing about integrality for ζ(7).** I have not independently rerun the paper's rational interval certificate.

As a numerical sanity check on that imported certificate, direct evaluation of the 16 rational arcsine components in its Table 1 gives total mass `0.925`, energy `I(ρ)≈-2.12659344514705`, and `C*≈2.65303599034049`. A 200001-point scan of `[0,2]` gives maximum `2U_ρ−V≈-6.64989388`, below the paper's stated `M=-6.645`; this scan is **not** a uniform proof and does not check the tail `t>2`.

The same scaling calculation works if the Hankel dimension is independent, say `H/K=β>0`, while `r/K=1-α` remains the number of `X`-dependent poles. Replace `λ` by `β` in (8)--(12), require the comparison measure to have mass `β`, and set

```
S_(K,N,q,H)=4^(H-1)(K!)^(2H)/[(N!)^(4qH)∏_(i=1)^(H-1)((2i)!)²],
C*(q,α,β)=-2β+4qαβ(1-log α)+3β²-2β²log(2β).
```

The raw and factorial `K²log K` coefficients are respectively `+2β(β+2qα-1)` and its negative, so they still cancel. If `H>=r`, the polynomial degree is exactly `r`, by the block argument above, while the potential problem has mass `β`. Whether the extra freedom in `β` improves the **combined** real and arithmetic exponent is open in this attempt.

## 4. Exact remaining irrationality target

For any sequence `K→∞` with `h=O(K)`, it is enough to prove that there are positive rational multipliers `m_K` such that

```
Q_K(X)=m_K S_(K,N,q) Δ_K(X) ∈ Z[X]
```

and, for one `c>0` and all sufficiently large `K`, `0<Q_K(ζ(7))<=exp(-cK²)`. By (12), a sufficient *unproved* arithmetic condition is

```
limsup_(K→∞) K^(-2)log m_K
       < -[λM-I(ρ)+C*(q,α)].                         (13)
```

If ζ(7)=a/b with integers `a`, `b>0`, then `b^h Q_K(a/b)` is a positive integer, while `b^hQ_K(a/b)<=exp(O(K)log b-cK²)→0`, a contradiction. This is the whole irrationality criterion: no coefficient-height estimate is required.

The crucial unresolved task is to establish (13) using **every coefficient** of `Δ_K(X)`, including polynomial quotient moments after partial fraction decomposition. The ζ(5) local prime estimates use fifth-order harmonic and Bernoulli cancellations that are not supplied by (1)--(12) for ζ(7). A positive Gram matrix and the ζ(5) potential bound alone cannot justify an irrationality claim. There is no analytic contradiction in the proposed ζ(7) formulas; the possible fatal obstruction is the arithmetic normalization cost exceeding the real decay.

## 5. Independent check of the outer-prime moment cutoff

This check addresses the condition `5N <= 2p-2` in the supplied paper's (4.9), which could otherwise be copied too restrictively into a ζ(7) calculation. For `s=7`, (1) is

```
μ_7(t^e)=(-1)^e B_(2e+2) [(2e+3)(2e+4)(2e+5)(2e+6)(2e+7)]/6!.
```

For every prime `p>=7`, von Staudt--Clausen says the only possible denominator contribution from `B_(2e+2)` is one factor `p`, and it occurs only if `p-1` divides `2e+2`. If `2e+2=k(p-1)` with `1<=k<=5`, the displayed numerator contains `2e+2+k=kp`, so the denominator cancels. Consequently

```
μ_7(t^e) ∈ Z_p  for every e<3p-4,                    (14)
v_p(μ_7(t^e)) >= -1  for all e>=0.
```

The first *possible* uncancelled denominator is at `e=3p-4`, corresponding to `k=6`; (14) is an integrality guarantee, not a claim that a denominator really occurs there. The ζ(5) paper has only three numerator factors, so its corresponding cutoff is `e<2p-3`.

For the `G` matrix, the polynomial quotient of `D_N^(2q)t^(i+j)/D_K` has degree at most `i+j+2qN-K`. Subtracting `c_e/p` from the moments of degree `e>=3p-4`, with `c_e∈Z_p` chosen so that the remaining moments are integral, produces a correction matrix `p^(-1)L` whose entries vanish whenever

```
i+j < K-2qN+3p-4.
```

Therefore an exact rank bound, over `Q_p` rather than merely modulo `p`, is

```
rank L <= max(0, K+(2q-2)N-3p+3).                   (15)
```

To express this as at most `h=K-N` without an extra `min(h,...)`, it suffices that `(2q-1)N<=3p-3`. For `q=4`, this is `7N<=3p-3`; the older `7N<=2p-2` would result from declining to use the two extra ζ(7) numerator factors. In the paper's `q=3, s=5` instance, the same algebra yields `5N<=2p-2` exactly. For `α=3/40` and `p>K/3`, both `2N<p` and the improved `7N<=3p-3` hold once `K` is large.

This rank calculation uses only the polynomial quotient. The *other* outer-prime hypotheses remain necessary for the paper-style residue analysis: `p²>2K` prevents nearby roots modulo `p²` from colliding in the relevant range, and `2N<p` keeps at most one removed pole in an ordinary square class. For two surviving poles `a,p-a`, the ζ(7) pole values are congruent modulo `p`: `H_(p-a)^(7) ≡ H_(a-1)^(7)` and the difference from replacing `H_a^(7)` by `H_(a-1)^(7)` contributes `a^6 a^(-7)=1/a`, canceled by the change in `1/(2j)`. This confirms the divided-difference step for odd exponent seven when all indices are `p`-units. The separate zero square class and the full determinant-weight sum are left to the arithmetic workstream.

## 6. Finite-class audit of the arithmetic integration code

`research/audit_arithmetic_counts.py` independently forms the ordinary square classes for `p=1009,10007,100003`, counts their poles, assigns the inner-row dimensions and outer-row weights, and evaluates the factorial valuation by Legendre's formula. It compares those finite counts against the limiting functions in `scripts/arithmetic_bounds.py` for `q=4, α=0.075`. At inner `x=3.17,5.73,11.21`, the largest absolute discrepancy falls from about `0.373` at `p=1009` to `0.00376` at `p=100003`. At outer `y=0.37,0.43,0.51,0.67,0.91,1.13,1.57`, the largest falls from `0.00506` to `0.0000510`. This is consistent with the expected `O(1/p)` finite-grid error and did not expose a branch omission at those points. The inner audit sets the fixed-size zero-square block to dimension zero, which changes only its `O(1/p)` comparison error; the full proof still needs the actual zero-block construction. Neither the sampled code check nor its floating quadrature certifies the limiting prime sum.
