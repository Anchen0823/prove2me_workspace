## Spencer's theorem with the exact degree, for positive line sums

Write `H_n(t)` for the number of `n × n` arrays of nonnegative integers whose every row and
every column sums to `t` (`MagicSquares.semiMagicCount n t` on the platform). The theorem
proved here is

```
theorem semi_magic_polynomial_exists_degree_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
```

for **every** order `n ≥ 1` uniformly — existence, *and* the degree is exactly `(n-1)²`, not
merely bounded by it.

This is the mission goal `MagicSquares.semi_magic_polynomial_exists` with one hypothesis added,
`1 ≤ t`. The addition is not cosmetic; see "What is not claimed" below.

### The route: Spencer's elementary proof, in four steps

`H_n(t)` is the Ehrhart polynomial of the Birkhoff polytope, so the *value* `(n-1)²` is forced
by BCCG's Theorem 1. The proof here nevertheless uses no Ehrhart theory, no quasi-polynomials
and no lattice-point machinery — Mathlib has none of those. It follows J. Spencer, *Counting
magic squares*, Amer. Math. Monthly **87** (1980) 397–399, whose content is generating functions
plus Hall's marriage theorem plus the finite poset of supports.

**1. The discrete antiderivative and the Spencer step** (`Spencer.lean`).

`exists_antideriv` produces, for every `P : ℚ[X]`, a polynomial `Q` with
`Q.natDegree ≤ P.natDegree + 1` and `Q.eval n = ∑_{m<n} P.eval m`, built as
`(B_{d+1}(X) - B_{d+1}) / (d+1)` from Mathlib's Faulhaber identity in Bernoulli-polynomial form
(`Polynomial.sum_range_pow_eq_bernoulli_sub`). `isPolyDegLe_of_recurrence` is the Spencer step:
a triangular recurrence with polynomial coefficients of degree `≤ K` exhibits its solution as a
polynomial of degree `≤ K+1`, by telescoping the recurrence into `b r = b 0 + ∑_{t<r} …` and
applying the antiderivative. `isPolyDegLe_of_recurrence_succ` is the same step in the shifted
indexing that the fibre recurrence actually has.

**2. Hall's theorem: a positive line-sum square contains a permutation** (`HallSupport.lean`).

`exists_perm_pos_of_line_sums`: a nonnegative integer matrix whose rows and columns all sum to
the same positive `t` has a permutation `σ` with `0 < M i (σ i)` for every `i`. This is Hall's
marriage theorem (`Finset.all_card_le_biUnion_card_iff_exists_injective`) applied to
`i ↦ {j : 0 < M i j}`; the Hall condition is `#s · t = ∑_{i∈s} (row i) ≤ ∑_{j∈N(s)} (col j) =
#N(s) · t`, which is exactly where positivity of `t` is consumed.

**3. The support recursion** (`SupportSplit.lean`, `Recursion.lean`).

Fix a permutation support `B`. Splitting `T ↦ T - P` (where `P` is the permutation matrix of
any `σ` with `φ(σ) ⊆ B`) off a square of line sum `s` gives

```
h_B(s+1) = h_B(s) + ∑_{C ∈ nb(B)} h_C(s),      nb(B) = {C : B \ φ(σ) ⊆ C ⊊ B},
```

`card_matFiber_recurrence_succ`. Note that `σ` is a *parameter* of the recurrence chosen once
per support set: any `σ` with `φ(σ) ⊆ B = supp T` automatically satisfies the positivity
hypothesis of the split, so one `σ` serves every line sum — which is what a recurrence with
constant coefficients requires. Strong induction on `B.card` then gives

```
isPolyDegLe_gB (n) (B) : IsPolyDegLe B.card (gB n B)
```

with no permutation inside `B` meaning the fibre is empty at every level (Hall), hence zero.

**4a. Aggregation — the bridge to the platform's own function** (`Aggregate.lean`).

The support fibres partition the semi-magic squares
(`semiMagicCount_eq_sum_matFiber`, from `card_matBoxLine` and
`Finset.card_eq_sum_card_fiberwise`), and shifting by one (`exists_poly_comp_X_sub_one`,
`p.comp (X - 1)`) turns the fractional-linear recursion variable back into the line sum. Result:
a polynomial of degree `≤ n²` agreeing with `H_n(t)` for `t ≥ 1`.

**4b. The sharp degree, upper bound** (`Rank.lean`, `Sharp.lean`).

Naively counting the recursion depth gives only `deg ≤ n² - n`, which overshoots by `n-1`. The
sharp bound needs the face rank `ρ(B) = |B| - v(B) + c(B)` of the Birkhoff polytope, formalised
here without any graph theory as

```
rankB B := dim {M : line sums 0, supp M ⊆ B}
```

with `rankB univ = (n-1)²` by rank–nullity on the line-sum map (whose range is the hyperplane
`Σrow = Σcol` of dimension `2n - 1`, surjectivity witnessed by the explicit transportation
matrix `M i j = (a(inl i) + a(inr j) - d/n)/n`). The strictness input is the **escape lemma**
`exists_zeroLine_touching`: if `φ(τ) ⊆ C` and `B \ φ(σ) ⊆ C ⊆ B` and `e ∈ B \ C`, then some
matrix of line sum zero, supported in `B`, is nonzero at `e`. Its proof is duality
(`LinearMap.range_dualMap_eq_dualAnnihilator_ker`) plus a two-summing contradiction — summing
`u i + v j = [ij = e]` over the `τ`-cells (all inside `C`) gives `Σu + Σv = 0`, over the
`σ`-cells (exactly one of which is `e`, since `e ∈ B \ C ⊆ φ(σ)`) gives `Σu + Σv = 1`. Both
hypotheses are needed: the bare statement "`φ(τ) ⊆ C ⊆ B`, `e ∈ B \ C` ⇒ `rankB C < rankB B`"
is **false**, with counterexample `B = φ(id) ∪ {bridge cell}`, `C = φ(id)`, where both ranks are
`0`; what rules the degenerate case out is precisely the candidate constraint `B \ φ(σ) ⊆ C`.
Degenerate candidates never contain a permutation, so their counts vanish identically. Result:
`natDegree ≤ (n-1)²`.

**4c. The matching lower bound — an explicit linear family** (`Degree.lean`).

For order `n+1` and line sum `(n+1)s`, take any `c : Fin n → Fin n → Fin (s/n + 1)` — that is
`n²` free parameters, each in a box of size `⌊s/n⌋ + 1` — and fill the `(n+1) × (n+1)` matrix by
putting `s + c p q` in the top-left `n × n` block and letting the line-sum equations determine
everything else:

```
M p q       = s + c p q            (block)
M p last    = s - ∑_q c p q        (last column)
M last q    = s - ∑_p c p q        (last row)
M last last = s + ∑_{p,q} c p q    (corner)
```

Every line sums to `n·s + Σc + (s - Σc) = (n+1)s`, and `c p q ≤ s/n` bounds `Σ_q c p q ≤ n⌊s/n⌋
≤ s`, so all entries are natural numbers. The construction is injective — the block is recovered
by `c p q = M p q - s` — hence

```
semiMagicCount_ge_family (n s : ℕ) (hn : 1 ≤ n) :
    (s / n + 1) ^ (n * n) ≤ semiMagicCount (n + 1) ((n + 1) * s)
```

Growth like `s^{(n-1)²}` then forces the degree through

```
le_natDegree_of_lowerBound {p : Polynomial ℚ} {d : ℕ} {A : ℚ} (hA : 1 ≤ A)
    (h : ∀ s : ℕ, 1 ≤ s → (s : ℚ) ^ d ≤ p.eval (A * (s : ℚ))) : d ≤ p.natDegree
```

which is deliberately elementary: at `x ≥ 1`, `p.eval x ≤ B · x^e` with `B = Σ|coeff|` and
`e = p.natDegree`; for `e < d` and `s` large, `s^d = s^{d-e} · s^e ≥ s · s^e` while the
hypothesis gives `s^d ≤ p.eval (A·s) ≤ B·A^e·s^e`; cancelling `s^e > 0` yields `s ≤ B·A^e`,
contradicting the choice of `s` (`exists_nat_gt`). No asymptotics, no analysis.

Combining 4b and 4c gives the claimed *equality* of degrees.

### What is not claimed, and why

Agreement at `t = 0`. The support-set recursion only ever sees *positive* line sums: a support
set is the support of some magic square, and the squares of line sum `0` only have the empty
support, for which there is no permutation inside `∅` — so `∅` is a base case rather than an
instance and the recursion has no term for it. Shifting the ladder (`g_B(r) := h_B(r+1)`) makes
the recursion homogeneous with `r = 0` as base, and yields a polynomial `q` with `q(r) = H_n(r+1)`
for all `r ≥ 0`; the value at `t = 0` is then `q(-1) = 1`. Writing `s_B := q_B(-1)`, the recursion
gives the triangular system `s_B = a_B - ∑_{C ∈ nb(B)} s_C` and the requirement is
`∑_{B ∈ X} s_B = 1` — verified by hand for `n = 2`, where `X = {D₁, D₂, Full}`, `s_{D₁} = s_{D₂} = 1`,
`s_{Full} = -1`. This is exactly **Ehrhart–Macdonald reciprocity at `-1`**, i.e. the statement
that `B_n` has no interior lattice points for `n ≥ 2`, which is the separate rung
`semi_magic_reciprocity` / `semi_magic_vanishing`. It is not a boundary triviality and it is not
reachable by the support-set route, so the goal `semi_magic_polynomial_exists` — which quantifies
over **all** `t : ℕ` — remains strictly stronger than this node.

### Formalization notes

* The file is a **bundle** of the eight modules under `examples/magic-squares/spencer/`
  (`Spencer`, `HallSupport`, `SupportSplit`, `Recursion`, `Aggregate`, `Rank`, `Sharp`,
  `Degree`), concatenated in topological order with a single import header; each module keeps its
  own `namespace MagicSquaresSpencer … end MagicSquaresSpencer` block. 2277 lines.
* No `sorry`, no `axiom`, no `admit`. `#print axioms` on the payoff theorems reports exactly
  `propext, Classical.choice, Quot.sound`.
* Compiles in **88 s** locally (well inside the 300 s limit); the only output is pre-existing
  linter warnings in `Rank.lean` (`unusedSimpArgs`, deprecated `Set.mem_setOf_eq` / `push_neg`).
* No published statement is edited by this node: `exists_polynomial_semiMagicCount_pos` (crude
  `n*n` bound) and `exists_polynomial_semiMagicCount_sharp` (`≤ (n-1)²`) are kept as separate
  declarations, and `exists_polynomial_semiMagicCount_degree_eq` is new.
