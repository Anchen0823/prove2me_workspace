# Proof sketch — Zudilin's theorem: at least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational

**Theorem (W. Zudilin, 2001).** At least one of the four numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational.
Equivalent formal statement: the set {5, 7, 9, 11} ∩ {a : ℕ | ζ(a) is irrational} is nonempty.

This submission is a *reduction* of the mission goal `FCP.Zeta.zudilin_five_seven_nine_eleven`
to four frontier children, all in the `ZudilinZeta` namespace:

1. `ZudilinZeta.exists_saddle_root_params13` (created with this submission);
2. `ZudilinZeta.zudilin_numeric_C0_gt_C1`;
3. `ZudilinZeta.zudilin_lemma3`;
4. `ZudilinZeta.zetaR_eq_riemannZeta` (created with this submission; proved in a separate submission).

Below is the mathematical argument, in the notation of the note [Z1]. It is a faithful
sketch: each numbered step is a lemma that is (or will be) a node of the mission.

## 1. The construction (Lemma 1 of the note; linear forms)

Let r = 3, q = 13 and take the parameters

  η₀ = 91,  η₁ = η₂ = η₃ = 27,  η₄ = 29,  η₅ = 30,  …,  η₁₃ = 38,

which satisfy η₁ ≤ … ≤ η₁₃ = 38 < 91/2 = 45.5 and η₁ + … + η₁₃ = 416 ≤ 91·(13−3)/2 = 455.
For n > 0 put h₀ = η₀n + 2, hⱼ = ηⱼn + 1 (1 ≤ j ≤ 13) and define the rational function

  Rₙ(t) = (h₀ + 2t) ∏_{j=1}^{3} Γ(hⱼ+t)/((hⱼ−1)! Γ(1+t)) · Γ(h₀+t)/((hⱼ−1)! Γ(1+h₀−hⱼ+t))
          ∏_{j=4}^{13} (h₀−2hⱼ)! Γ(hⱼ+t)/Γ(1+h₀−hⱼ+t).

Since Rₙ(t) = O(t⁻²), the series Fₙ = (1/2!) ∑ₜ Rₙ⁽²⁾(t) converges; expanding Rₙ in
partial fractions turns it into a rational linear combination of 1 and the odd zeta
values ζ(5), ζ(7), ζ(9), ζ(11) (the intermediate and even terms cancel by the choice
of parameters). This is the content of **Lemma 1** of [Z1].

## 2. Integrality and the denominator (Lemma 1, (3))

With D_N = lcm(1,…,N) and the functions mⱼ, φ, Φₙ defined as in the note, Lemma 1
asserts the arithmetic form

  Λₙ := D^3_{m₁n} D_{m₂n} ⋯ D_{m₁₀n} · Φₙ⁻¹ · Fₙ ∈ ℤ + ℤζ(5) + ℤζ(7) + ℤζ(9) + ℤζ(11).

The growth rates are: log D_{mⱼn}/n → mⱼ (prime number theorem) and log Φₙ/n → ϖ,
where ϖ = ∫₀¹ φ dψ − ∫₀^{1/m₁₀} φ(x)/x² dx is evaluated by the Chudnovsky–Rukhadze–Hata
method. Hence the denominators of Λₙ grow at most like e^{C₁n+o(n)} with

  C₁ = 3m₁ + m₂ + … + m₁₀ − ϖ = 226.24944266…

(this is the arithmetic part of the note; the value of C₁ is recorded in the node
`zudilin_numeric_C0_gt_C1`).

## 3. The asymptotic decay (Lemma 2 of the note)

Let τ₀ be the saddle point: the root of

  (τ−η₀)³ (τ−η₁) ⋯ (τ−η₁₃) − τ³ (τ−η₀+η₁) ⋯ (τ−η₀+η₁₃) = 0

in the upper half-plane of maximal real part, with Re τ₀ < η₀ and Im f₀(τ₀) ∉ πℤ,
where f₀ is the auxiliary function of the note. The complex-integral representation
of Fₙ (residues on the line Re t = const) and Stirling's formula give, by the saddle-point
method,

  limsup log|Fₙ|/n = Re f₀(τ₀) = −C₀,  C₀ = 227.58019641…

The condition Im f₀(τ₀) ∉ πℤ moreover guarantees that the leading asymptotic
coefficient is nonzero, so Fₙ ≠ 0 (hence Λₙ ≠ 0) for all large n. The existence of τ₀
with these properties for the parameters above is the node
`exists_saddle_root_params13`; the numeric values of C₀ and C₁ are the node
`zudilin_numeric_C0_gt_C1` (read as 227.58019641 ≤ C₀ < 227.58019642 and
226.24944266 ≤ C₁ < 226.24944267).

## 4. The diophantine criterion (Lemma 3 of the note; elementary)

Since C₁ < C₀ (the margin is C₀ − C₁ ≈ 1.3308), we get |Λₙ| ≤ e^{(C₁−C₀+o(1))n} → 0,
while Λₙ ≠ 0 is an integer-coefficient linear form in 1, ζ(5), ζ(7), ζ(9), ζ(11).
**Criterion.** If all four zeta values were rational with common denominator Q, then
Λₙ ∈ (1/Q)ℤ, so Λₙ ≠ 0 would force |Λₙ| ≥ 1/Q, contradicting |Λₙ| → 0.
Hence at least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational. This is **Lemma 3** of the
note, instantiated at r = 3, q = 13: it outputs k ∈ {1,2,3,4} with
Irrational(zetaR(3 + 2k)), i.e. an irrational among ζ(5), ζ(7), ζ(9), ζ(11).

## 5. Bridging to Mathlib's riemannZeta

The goal is stated with Mathlib's complex `riemannZeta`, whereas the linear-form layer
uses the elementary series zetaR k = ∑ₙ (n+1)⁻ᵏ. For k ≥ 2 the two agree
(zeta_eq_tsum_one_div_nat_add_one_cpow + cpow_natCast + ofReal_tsum); this is the node
`zetaR_eq_riemannZeta`, proved in a separate submission. Transferring the irrationality
along this identification and using 3 + 2k ∈ {5,7,9,11} for k ∈ {1,2,3,4} closes the goal.

## 6. What a verifier must check

The reduction above is the skeleton; the following checks discharge the open children:

- `exists_saddle_root_params13` — existence of the saddle point τ₀ (root of the
  degree-13 saddle polynomial, upper half-plane, maximal real part, Re τ₀ < 91,
  Im f₀(τ₀) ∉ πℤ). Verified numerically (C₀ = −Re f₀(τ₀) matches 227.58019641…);
  a rigorous proof uses a sign/existence argument on the polynomial and interval
  arithmetic for the inequalities.
- `zudilin_numeric_C0_gt_C1` — rigorous bounds 227.58019641 ≤ C₀ < 227.58019642,
  226.24944266 ≤ C₁ < 226.24944267 (high-precision evaluation of the saddle point and
  the Stieltjes integral defining C₁, with rigorous error control).
- `zudilin_lemma3` — the elementary criterion of §4 (fully self-contained) combined
  with the asymptotic and arithmetic lemmas: |Λₙ| = e^{(C₁−C₀+o(1))n}, Λₙ ≠ 0.
- `zetaR_eq_riemannZeta` — proved (submitted separately): two lines of series
  manipulation on top of Mathlib's Dirichlet-series identity.

## References

[Z1] W. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational,
Uspekhi Mat. Nauk 56:4 (2001), 149–150; English transl. Russian Math. Surveys 56:4
(2001), 774–776, https://doi.org/10.4213/rm427 .
[Z2] W. Zudilin, Irrationality of values of the Riemann zeta function, Izv. Math. 66:3
(2002), 489–542 (full proofs of the arithmetic lemmas).
