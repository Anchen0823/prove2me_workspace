# Round 2: layered numerator and shifted Gram space for ζ(7)

Status (2026-09-24): the algebraic and analytic statements below are proved under their explicit hypotheses. They provide **no irrationality proof** without a matching integer-polynomial normalization and a strictly negative final exponent. The notation permits several layers and an independent matrix size; the old one-layer construction is recovered by taking one pair `(N,q)`, `g=0`, and `h=K-N`.

## 1. Exact algebraic structure

Fix a finite number `A` of layers, integers `0 <= N_a < K` and `q_a >= 1` (`1 <= a <= A`), and let `N_* = max_a N_a`, `r=K-N_*`. Put

```
D_m(t) = ∏_(j=1)^m (t+j²),
P(t) = ∏_(a=1)^A D_(N_a)(t)^(2q_a),
F(t) = P(t)/D_K(t).
```

The empty product is one. `P/D_K` has no pole at `-j²` for `j<=N_*`, since some layer with `N_a=N_*` supplies a positive even power there; it has a simple pole at every `-j²`, `N_*<j<=K`. It is positive for `t>=0`.

For any `h>=1` and integer `g>=0`, set `e_i=g+i` for `0<=i<h` and define

```
G_ij(X) = μ_X(F(t)t^(e_i+e_j)),
Δ_(K,h,g)(X) = det_(0<=i,j<h) G_ij(X),
```

where `μ_X` is the ζ(7) functional from `analytic-foundations.md`: its polynomial moments are rational and its values at simple poles `1/(t+j²)` belong to `Q+QX`. Polynomial division therefore proves **entrywise** `G_ij(X)∈Q+QX`; no other ζ value is introduced. More generally, the same claim holds for any distinct nonnegative exponent set `E={e_0<...<e_(h-1)}`.

At `X=ζ(7)` the entries are integrals against the positive weight `w_7(y)dy`. For every nonzero `c∈R^h`, the sparse polynomial `Q_c(t)=Σ_i c_i t^(e_i)` is not identically zero, and

```
cᵀG(ζ(7))c = ∫_0^∞ F(y²) Q_c(y²)² w_7(y)dy >0.
```

Thus `G(ζ(7))` is positive definite and `Δ_(K,h,g)(ζ(7))>0` for every choice above, even if `Q_c(0)=0` because of the shift.

Let `z_j=-j²` for `N_*<j<=K`. The pole residue of `F(t)t^(e_i+e_j)` at `z_j` is `z_j^(e_i+e_j)P(z_j)/D_K'(z_j)`, so its `X` coefficient is

```
B_ij := [X]G_ij
      = Σ_(j=N_*+1)^K c_j z_j^(e_i+e_j),
c_j = j^6 P(z_j)/D_K'(z_j) ∈ Q\{0}.
```

Equivalently `B=V_E diag(c_j)V_Eᵀ`, with `(V_E)_(i,j)=z_j^(e_i)`. Multiplying row `i` by `(-1)^(e_i)` turns `V_E` into the generalized Vandermonde matrix `((j²)^(e_i))`. Its rank is `min(h,r)`: every square minor formed from distinct positive nodes and strictly increasing exponents is nonzero. One elementary proof is that a nonzero polynomial with at most `m` monomials has at most `m-1` distinct positive roots by Descartes' sign rule. In particular,

```
deg_X Δ_(K,h,g) <= min(h,r).                             (A)
```

Positivity improves this to an **exact rank identity** for every exponent set, even when `B` is indefinite:

```
deg_X Δ_(K,h,g) = rank_R B.                                (A*)
```

Indeed let `G_0=G(ζ(7))`, which is positive definite. Writing `G(X)=G_0+(X-ζ(7))B` and conjugating by `G_0^(-1/2)` gives `det G(X)=det G_0·det(I+(X-ζ(7))C)` with `C=G_0^(-1/2)BG_0^(-1/2)` real symmetric. It has exactly `rank B` nonzero real eigenvalues, so the product has exactly that degree.

If `h>=r`, equality holds. Indeed `V_E` has full column rank `r`, hence `B` has rank `r` despite the possibly alternating signs of `c_j`. A rational change of basis splits the `h`-dimensional polynomial space into an `r`-dimensional complement of `ker B` and its `(h-r)`-dimensional kernel. Since `B=V_E diag(c_j)V_Eᵀ` and `V_E` has full column rank, `ker B=ker V_Eᵀ`: these are precisely the polynomials in the chosen space that vanish at all `z_j`, or equivalently are divisible by `D_K/D_(N_*)`. Every matrix entry involving such a polynomial is independent of `X`, because all simple-pole residues vanish. The lower-right Gram block `C` on this kernel is therefore constant in `X` and positive definite at `X=ζ(7)`. The upper-left `X` coefficient `B_r` is invertible. The leading determinant coefficient is `det(B_r)det(C)≠0`, proving

```
h>=r  ==>  deg_X Δ_(K,h,g)=r.                            (B)
```

For `h<r`, (A*) is the safe exact statement. The `c_j` need not have one sign, so full row rank of `V_E` by itself does **not** prove `rank B=h`; cancellation in `V_E diag(c_j)V_Eᵀ` must be checked. In the especially useful case `h=r`, `(B)` follows immediately from `det B=(det V_E)²∏c_j≠0`.

There is an exact residue-at-infinity test that can reveal such cancellation *before* forming a determinant. Since `j^6=(-z_j)^3=-z_j³`, the sum of the finite residues gives

```
B_ij = -[t^(-1)]_(t=∞) { t^(e_i+e_j+3) P(t)/D_K(t) }.   (B∞)
```

Here `[t^(-1)]` means the coefficient in the Laurent expansion at infinity. If `d=deg P=2Σ_a q_aN_a`, then this coefficient vanishes whenever `e_i+e_j+d-K+3 < -1`, equivalently

```
e_i+e_j < K-d-4.                                         (B0)
```

This proves that `deg<=min(h,r)` can be very loose for `h<r`. For example, let all `N_a=0`, take `h=1`, `g=0`, and `K>=5`: then `G_00(X)` is rational, with zero `X` coefficient, although `r=K`. An overall shift may bring the coefficient back into range by increasing `e_i+e_j`; its effect is not simply a basis change. This residue test does not replace the positive-Gram or integerization arguments.

For the uniform shift there is one exact nonvanishing threshold worth testing. Put `T=K-d-4-2g`. If `T=h-1`, then `(B0)` gives `B_ij=0` for `i+j<h-1`, while `(B∞)` gives `B_ij=-1` for every `i+j=h-1`, because `P` and `D_K` are monic and the Laurent term there starts with `t^(-1)`. Reversing the columns makes `B` triangular with diagonal `-1`, so

```
2g+h+d=K-3  ==>  det B=(-1)^[h(h+1)/2] !=0,
                       deg_X Δ_(K,h,g)=h.                 (B1)
```

This regime necessarily has `h<r` when the layers are nonempty: since `d>=2N_*`, its equality forces `h<=K-2N_*-3-2g<K-N_*`. It offers a leading `X` coefficient of absolute value one, though the lower coefficients and whole determinant can still have expensive denominators. If `T>h-1`, the first row of `B` vanishes, so the highest possible `X^h` coefficient is zero. Thus a naive small-`h` family can silently lose its intended polynomial degree.

More generally, if `h-1<=T<=2h-2`, the first `T-h+1` rows and columns vanish. The remaining `m=2h-1-T` square block has zeros for `i+j<T` and entries `-1` along `i+j=T`, so it is invertible by reversing its columns. Therefore `(A*)` yields the **exact degree**

```
h-1<=T<=2h-2  ==>  deg_X Δ_(K,h,g)=2h-1-T;
T>2h-2         ==>  deg_X Δ_(K,h,g)=0.              (B2)
```

For `T<h-1`, this anti-triangular argument does not determine `rank B`; `(A*)` remains exact once that rational-matrix rank is computed.

The zero-degree region in `(B2)` is a **rigorous obstruction** to this determinant family: `Δ_(K,h,g)(X)` is then a positive rational constant. Any positive scalar that makes it an integer produces a value at least one, so no real-side decay estimate can yield the desired integer-polynomial contradiction there. This excludes that part of parameter space before any potential-theory or prime-sum computation.

### A fixed-degree window and a rational upper approximant

The anti-triangular regime also admits a fixed positive degree while `K,h,g` grow. Let a fixed integer `m>=1` satisfy

```
2h = K-d-2g-3+m,   h>=m,   d=2Σ_a q_aN_a.           (B3)
```

Then `T=2h-1-m` lies between `h-1` and `2h-2`, so `(B2)` proves `deg_X Δ=m`. The first `h-m` rows and columns of `B` vanish: if `i<h-m` and `j<h`, then `i+j<=2h-m-2<T`. In the resulting block decomposition,

```
G(X) = [ Q       U      ]
       [ Uᵀ  C_0+X B_m ],
```

`Q` and `U` are rational and independent of `X`; `Q` is positive definite because it is a principal block of `G(ζ(7))`. The bottom `m×m` matrix `B_m` has `-1` on its anti-diagonal and zeros below it, hence is invertible. Consequently

```
Δ(X)=det(Q) det(C_0-UᵀQ^(-1)U+X B_m),             (B4)
```

a rational polynomial of exact degree `m` that is positive at `X=ζ(7)`. If `m` remains fixed along a parameter sequence, a primitive integer multiple `P_K(X)` would prove irrationality whenever `0<P_K(ζ(7))→0`; no `K²` decay rate is logically necessary because a putative denominator `b` of ζ(7) contributes only the fixed factor `b^m`. This is a **conditional criterion**, not an established asymptotic for `P_K`.

For `m=1`, condition `(B3)` makes `B=-e_(h-1)e_(h-1)ᵀ` exactly. Writing the rational lower-right constant as `c` and the rational cross vector as `u`, `(B4)` becomes

```
Δ(X)=det(Q)(R_K-X),
R_K=c-uᵀQ^(-1)u ∈Q,
R_K>ζ(7).                                                (B5)
```

The strict inequality is the positive Schur complement of `G(ζ(7))`. Moreover

```
R_K-ζ(7)
 = min_(a_0,...,a_(h-2)∈R) ∫_0^∞ F(y²)
       [y^(2(g+h-1))+Σ_(i=0)^(h-2) a_i y^(2(g+i))]² w_7(y)dy.
```

Thus `R_K` is a rigorously defined rational **upper** approximation and its error is a weighted least-squares minimum. Neither the size of its reduced denominator nor the decay of the corresponding primitive integer linear form follows from positivity alone; those remain the decisive arithmetic and asymptotic tests. For `m=3,5` the same fixed-degree block argument applies, without producing a single rational approximant.

The same argument applies to the two-block exponent set `E={0,...,h_0-1}∪{h_0+g,...,h+g-1}` with `0<=h_0<=h`: positivity, affine single-ζ entries, (A), and exact degree for `h>=r` survive unchanged. A unimodular change of basis inside the *same* polynomial space leaves the determinant unchanged, so it cannot itself improve the construction.

## 2. Shifted multilayer external field

Take a scaling sequence with `N_a/K=α_a+O(1/K)`, `h/K=β+O(1/K)`, `g/K=γ+O(1/K)`, where `α_a∈[0,1)`, `β>0`, `γ>=0` are fixed, and the number and multiplicities of layers stay fixed. Write

```
J_α(t) = ∫_0^α log(t+u²)du
       = α log(t+α²)-2α+2√t arctan(α/√t)       (t>0),
J_0(t)=0,
V_(α,q,γ)(t) = 2π√t + J_1(t) - 2Σ_a q_a J_(α_a)(t) - 2γ log t.     (C)
```

The limit of `J_α` at zero is `2α(log α-1)` for `α>0`, and `J_α(t)=α log t+O(1/t)` at infinity. Therefore `V(t)→+∞` at both endpoints if `γ>0`; at infinity its leading growth is always `2π√t`. The derivative, useful for locating a support or certifying tails, is

```
V'(t) = [π+arctan(1/√t)-2Σ_a q_a arctan(α_a/√t)]/√t -2γ/t.   (D)
```

No one-interval or one-well assertion follows from (D) for arbitrary layers.

For shifted monomials, Andréief's identity gives

```
Δ_(K,h,g)(ζ(7)) = (1/h!) ∫_(0,∞)^h
  ∏_(i<j)(y_i²-y_j²)² · ∏_i y_i^(4g) F(y_i²) w_7(y_i)dy_i.
```

With `y_i=K√t_i`, the Vandermonde contributes `K^(2h(h-1))`, the numerator/denominator contributes `K^[2h(2Σ_a q_aN_a-K)]`, and the shift contributes `K^(4gh)`. The weight, Jacobian, `h!`, and the finite-layer Riemann-sum errors are `exp(O(K log K))` at the scale considered here. The leading scale is thus

```
log Δ_(K,h,g)(ζ(7))
 <= 2β(β+2Σ_a q_aα_a+2γ-1)K²log K
    + [βM-I(ρ)]K² + O(K log K),                          (E)
```

provided a positive comparison measure `ρ` of mass `β`, compactly supported inside `(0,∞)`, has finite logarithmic energy `I(ρ)` and satisfies `2U_ρ(t)-V(t)<=M` for all `t>0`, with sufficient local regularity for the circle-regularization error used in `analytic-foundations.md`. The argument is the same zero-mass logarithmic-energy bound as before. For `γ>0`, the two tails of `2U_ρ-V` tend to `-∞`, so a rigorous inequality certificate only needs a finite middle interval plus explicit endpoint estimates. For `γ=0`, the hard edge at zero remains to be checked directly.

## 3. Factorial normalization and the exact real target

A natural rational scalar for matching shifted row arithmetic is

```
S_(K,h,g,Na,qa) =
  4^(h-1)(K!)^(2h) /
  [ (∏_a (N_a!)^(4q_a h)) · (∏_(i=0)^(h-1)((2(g+i))!)²) ].       (F)
```

Let `F_0(x)=3x²-2x²log(2x)` for `x>0`, with `F_0(0)=0`. Stirling summation gives

```
log S = -2β(β+2Σ_a q_aα_a+2γ-1)K²log K
        + C*(α,q,β,γ)K² + O(K log K),

C* = -2β +4βΣ_a q_aα_a(1-log α_a)
     +F_0(γ+β)-F_0(γ),                                  (G)
```

using `α log α=0` at `α=0`. To verify the new term directly, the logarithm of the shifted factorial denominator has leading part

```
4K² ∫_γ^(γ+β) x[log K+log(2x)-1]dx;
```

its negative contributes `-(4γβ+2β²)K²log K+F_0(γ+β)-F_0(γ)`. Thus the `K²log K` terms in (E) and (G) cancel exactly. In particular,

```
log [S Δ_(K,h,g)(ζ(7))]
 <= [C*+βM-I(ρ)]K²+O(K log K).                         (H)
```

If `ρ` is a true equilibrium measure and satisfies `2U_ρ-V=M` on its support, then `βM-I(ρ)=I(ρ)-∫Vdρ`; the real target becomes `C*+sup_(mass σ=β)(I(σ)-∫Vdσ)`. For a proposed discrete arcsine comparison measure, (H) only needs the upper inequality `2U_ρ-V<=M`, not an exact equilibrium proof.

The scalar (F) is a convenient normalization, not an arithmetic theorem. For any positive rational `c_K`, replacing `S` by `c_KS` simply replaces a minimal integerization multiplier `m_K` by a compensating factor; its apparent real-side gain or loss is not invariant. The invariant task is to find positive rational `m_K` with

```
Q_K(X)=m_K S Δ_(K,h,g)(X) ∈ Z[X]
```

and prove `limsup K^(-2)log m_K < -[C*+βM-I(ρ)]`. Because `deg Q_K<=r=O(K)`, positivity and the standard rationality contradiction then apply. None of the analytic formulas estimates `m_K`.

## 4. Two-block gaps versus an overall shift

For `E={0,...,h_0-1}∪{h_0+g,...,h+g-1}`, put `m=h-h_0`. The alternant identity is

```
det_(0<=i<h,1<=j<=h)(t_j^(e_i))
   = ± ∏_(i<j)(t_j-t_i) · s_((g^m))(t_1,...,t_h),         (I)
```

where `s_((g^m))` is a rectangular Schur polynomial of homogeneous degree `gm` and has nonnegative coefficients on `t_j>=0`. Under `y=K√t` its square adds `K^(4gm)` and a residual `s_((g^m))(t)^2`. For fixed `g` this residual changes only lower-order asymptotics; with `g,m` proportional to `K` it is a genuine `K²` many-particle term. The old scalar (F) for a uniform shift does not normalize this two-block alternant automatically, and the old one-body external field is insufficient.

If `t_(1)>=...>=t_(h)>0` denote ordered particles, the tableau expansion gives the useful but potentially coarse bound

```
∏_(j=1)^m t_(j)^g
 <= s_((g^m))(t)
 <= s_((g^m))(1^h) ∏_(j=1)^m t_(j)^g.               (J)
```

The Weyl dimension factor is explicit:

```
log s_((g^m))(1^h)
 = Σ_(i=1)^m Σ_(j=m+1)^h log(1+g/(j-i)).               (K)
```

For macroscopic `g,m,h`, (K) is generally `Θ(K²)`, so the upper bound may erase the desired gain. If `g=O(1)` and `h=O(K)`, then (K) is `O(K)` by `log(1+x)<=x` and `Σ_(i<=m<j)(j-i)^(-1)=O(h)`; the entire Schur effect is below the `K²` energy scale after accounting for `K^(4gm)`. A macroscopically useful two-block gap therefore requires a new Schur-aware variational estimate and a new prime-by-prime normalization.

The uniform shift `h_0=0` is the tractable special case: `s_((g^h))(t)=∏_j t_j^g`, so its entire real effect is exactly the one-body `-2γ log t` in (C). It changes the polynomial space, unlike a primitive basis replacement, while retaining a standard weighted logarithmic-energy problem. It may or may not improve the combined real and arithmetic exponent.

There is a useful sensitivity identity for screening shifts. Let `E(γ)=sup_(mass σ=β)[I(σ)-∫V_(α,q,γ)dσ]` over finite-energy measures. It is convex in `γ`, being a supremum of affine functions. At a value `γ>0` where the maximizing measure `ρ_γ` is unique and the envelope is differentiable,

```
E'(γ)=2∫log t dρ_γ(t),
(C*)'(γ)=4[(γ+β)(1-log(2(γ+β)))-γ(1-log(2γ))].       (N)
```

The first formula follows by evaluating the same maximizing measure at neighboring `γ` and taking the two one-sided bounds; the second is differentiation of (G). Hence the slope of the *real* normalized exponent `C*+E` is available from a candidate equilibrium measure without rederiving the full asymptotic formula. It says nothing by itself about the slope of the arithmetic multiplier `m_K`, which is indispensable for a proof.

## 5. Additional check relevant to a candidate shift

The shift cannot be assessed from the old $p$-adic table unchanged. In the polynomial quotient of `F(t)t^(e_i+e_j)`, the highest moment degree is `e_i+e_j+2Σ_a q_aN_a-K`; the ζ(7) Bernoulli integrality guarantee ends at degree `3p-5` (first possible nonintegral moment at `3p-4`). Consequently an outer-prime correction matrix has zero `(i,j)` entry whenever

```
e_i+e_j < K-2Σ_a q_aN_a+3p-4.                     (L)
```

For the uniform shift, (L) moves the threshold by `2g`; a conservative rank bound in the common regime is

```
rank L <= min(h, max(0,2h+2g-K+2Σ_a q_aN_a-3p+3)),      (M)
```

with the exact small-offset convention following from `(L)`. This is only a structural upper bound; it is not a determinant valuation theorem. In ordinary `p`-unit pole classes, multiplication by `t^(2g)` supplies no automatic valuation gain. The zero square class can gain powers of `p` in its pole residues, but the polynomial-moment part need not share that gain, so the whole matrix entry cannot simply be credited with `4g` extra valuation. Any decisive claim must account for both effects in the exact integerization multiplier. An analytically promising `γ` is therefore a candidate for arithmetic audit, not evidence of an irrationality proof.
