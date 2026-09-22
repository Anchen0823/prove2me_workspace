# The Spencer route to `semi_magic_polynomial_exists`

> **Continuation, 2026-09-20:** the positive-line-sum restriction has been removed by closed-support induction; negative-integer vanishing is also proved locally. See [CLOSED-SUPPORT.md](CLOSED-SUPPORT.md), `ClosedPolynomial.lean`, and `ClosedVanishing.lean`. Earlier descriptions of S5 as still open below are historical; consult [status.md](status.md) for current verification and platform state.


Working notes for Mission V, rung `M5`.  Written 2026-09-19 after reading the source and
scouting Mathlib.  **Read this before writing any code for `semi_magic_polynomial_exists`,
`semi_magic_reciprocity` or `semi_magic_vanishing`.**

## 1. The source and the route

J. Spencer, *Counting magic squares*, Amer. Math. Monthly **87** (1980) 397–399.
The zbMATH review (0465.05005) states the content exactly:

> A magic square of size n and order n is defined to be an n × n matrix A with nonnegative
> integral coefficients such that every row and column sums to r.  **An elementary proof is
> given that for each fixed n the number of such squares is polynomial in r.**

Keywords listed: *magic square; marriage theorem*.  So the proof is
**generating functions + Hall's marriage theorem + a finite poset of supports** — no power
series analysis, no polytopes, no Ehrhart theory.  This is why it is the only realistic route
to the general-`n` rung: Mathlib has no Ehrhart / quasi-polynomial / lattice-point machinery
at all, but it does have Hall and it does have everything below.

The proof is standard enough that it is handed out as a course exercise.  The clean write-up is
in R. Lalley's *Exercise Set 1: Magic Squares* (Chicago, MATH 388), which splits it into four
steps:

1. **Partial fractions.**  If `G(z) = Σ b(n) zⁿ = R(z)/(1-z)^m` with `deg R < m` and
   `R(1) ≠ 0`, then `b(n)` is a polynomial in `n` of degree `≤ m - 1`.
2. **Poset recursion.**  Let `(X, ≤)` be a finite poset and suppose generating functions
   `H_x` satisfy `H_x = a_x + z H_x + z Σ_{y<x} b_{x,y} H_y` for constants `a_x, b_{x,y}`.
   Then every `H_x` is of the form (1), so every `h_x(n)` is a polynomial.
3. **Support sets.**  `X` = the support sets `B(T) = {(i,j) : T(i,j) ≥ 1}` of magic squares,
   ordered by inclusion; `h_B(n)` = number of magic squares of weight `n` with support exactly
   `B`.  Birkhoff–von Neumann gives, for each `B ∈ X`, the support `φ(B) ⊆ B` of a permutation
   matrix, and the recursion holds with `a_B = 1` iff `B = φ(B)`, `b_{B,C} = 1` iff
   `B - φ(B) ⊆ C ⊊ B`.
4. **Degree.**  `deg h_B ≤ (n-1)²`.

## 2. Mathlib inventory (verified by grep, 2026-09-19)

Everything the *analytic-looking* half of the proof needs is already there and, crucially, in
**exactly the right form**:

| what | where | note |
|---|---|---|
| Faulhaber in Bernoulli-polynomial form | `Polynomial.sum_range_pow_eq_bernoulli_sub` (`NumberTheory/BernoulliPolynomials.lean:160`) | `(p+1) * Σ_{k<n} k^p = (bernoulli p.succ).eval n - bernoulli p.succ` |
| the same, rearranged | `Polynomial.bernoulli_succ_eval` (line 177) | `(bernoulli p.succ).eval n = bernoulli p.succ + (p+1) * Σ_{k<n} k^p` |
| `natDegree (bernoulli n) ≤ n` | *not* in Mathlib; follows in 3 lines from `Polynomial.coeff_bernoulli` (line 62) | proved in `Spencer.lean` |
| `1/(1-X)^d` as a unit | `PowerSeries.invOneSubPow`, `PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose` (`RingTheory/PowerSeries/WellKnown.lean:106,125`) | `(invOneSubPow S (d+1)).val = mk (fun n => Nat.choose (d+n) d)` — available but **not needed** on the discrete route |
| degree bounds for sums / `C *` / subtraction | `Polynomial.natDegree_sum_le_of_forall_le`, `Polynomial.natDegree_C_mul_le`, `Polynomial.natDegree_le_iff_coeff_eq_zero`, `Polynomial.coeff_eq_zero_of_natDegree_lt` | all in `Algebra/Polynomial/` |
| monomial-to-coefficient expansion | `Polynomial.eval_eq_sum_range`, `eval_eq_sum_range'` (`Eval/Degree.lean:63,67`) | |
| Hall's theorem | `Finset.all_card_le_biUnion_card_iff_exists_injective` and friends | for step 3 |
| permutation matrices | `Matrix.Permutation`, `Matrix.permutationMatrix` | for step 3 |
| support/poset induction | `Finset` + well-founded recursion | for step 3 |

Two consequences worth stating plainly:

* **Mathlib has no Faulhaber-free way to do this.**  Without `sum_range_pow_eq_bernoulli_sub` the
  discrete antiderivative would be a serious project on its own (the "falling factorial
  telescoping" route needs a spanning argument for the binomial basis).  With it, the whole
  analytic half collapses to ~60 lines.
* **Do not reach for `PowerSeries`.**  It exists and looks tempting, but the coefficient of
  `P · (1-X)^{-(k+1)}` involves a *truncated* `n - j`, which is exactly the boundary nuisance
  that the discrete formulation avoids.  The discrete formulation is the one to use.

## 3. What is already proved

`examples/magic-squares/spencer/Spencer.lean` (182 lines, clean, no `sorry`, no `axiom`):

* `natDegree_bernoulli_le`, `natDegree_sub_C_le`, `bernoulliAntideriv`,
  `bernoulliAntideriv_natDegree`, `bernoulliAntideriv_eval` — the Bernoulli antiderivative of
  `X ^ d` is `(B_{d+1}(X) - B_{d+1}) / (d+1)`, of degree `≤ d + 1`, with
  `(bernoulliAntideriv d).eval n = Σ_{m<n} m^d`;
* `antideriv`, `antideriv_natDegree`, `antideriv_eval`, `exists_antideriv` —
  **the discrete antiderivative**: for every `P : ℚ[X]` there is `Q` with
  `Q.natDegree ≤ P.natDegree + 1` and `Q.eval n = Σ_{m<n} P.eval m`;
* `IsPolyDegLe`, `isPolyDegLe_const`, `isPolyDegLe_mono`, `isPolyDegLe_sum`,
  `isPolyDegLe_of_recurrence` — **the Spencer step**: a triangular recurrence with polynomial
  coefficients of degree `≤ K` produces a polynomial of degree `≤ K + 1`, by telescoping to
  `b r = b 0 + Σ_{t<r} …` and applying the antiderivative;
* `isPolyDegLe_of_recurrence_succ` — the same step in the *shifted* indexing
  `b (r+1) = b r + Σ_i c i r`, which is the shape the fibre recurrence actually has.  Writing the
  recurrence with `r - 1` on the right costs a case split at every use site; this form does not.
  (Added 2026-09-19 while landing S2d.)

This is steps 1 and 2 of the four, in the discrete rather than the power-series language.

`examples/magic-squares/spencer/HallSupport.lean` (68 lines, clean) is the **first half of
step 3**:

* `exists_perm_pos_of_line_sums` — a nonnegative integer `n × n` matrix whose rows and columns
  all sum to the same **positive** `t` has a permutation `σ` with `0 < M i (σ i)` for all `i`.
  Hall's marriage theorem (`Finset.all_card_le_biUnion_card_iff_exists_injective`) applied to
  `i ↦ {j : 0 < M i j}`; the Hall condition is `#s * t = Σ_{i∈s}(row i) ≤ Σ_{j∈N(s)}(col j) = #N(s) * t`,
  which is where `0 < t` is used.  Converting the injective `Fin n → Fin n` into an
  `Equiv.Perm (Fin n)` is `Fintype.bijective_iff_injective_and_card` + `Equiv.ofBijective`.

`examples/magic-squares/spencer/SupportSplit.lean` (401 lines, clean) is the **technical core of
step 3**: the split `T ↦ T - P`, and — added after this note was first written — the whole cardinal
assembly that turns it into the recurrence.  See §7 for the details and for the ambient-bound
bookkeeping that made it statable.

`examples/magic-squares/spencer/Recursion.lean` (244 lines, clean) **completes step 3** — rung S2d.
It contains:

* `matFiber_eq_of_le` — the ambient bound is redundant once the line sum is known, which is the
  cancellation S2c owed;
* `exists_perm_support_subset_of_lineSums` — Hall, in the form the recursion consumes: a square of
  positive line sum has a permutation inside its support.  Because `φ ⊆ B = supp T` makes the
  hypothesis `0 < T i (σ i)` of `SupportSplit.lean` automatic, *one* `σ` per support set `B` serves
  every line sum — which is what a recurrence with constant coefficients requires;
* `nbSupp`, `card_matFiber_recurrence_succ` — the recurrence of §7.1 with the bound cancelled and
  written in the shifted shape `fibre(s+1) = fibre(s) + Σ_{C ∈ nb} fibre(s)`;
* `gB`, `card_matFiber_zero`, `isPolyDegLe_gB_empty`, and the main

  ```lean
  theorem isPolyDegLe_gB (n : ℕ) (B : Finset (Fin n × Fin n)) :
      IsPolyDegLe B.card (gB n B)
  ```

  by strong induction on `B.card` (`Nat.strong_induction_on`, since Mathlib has no
  `Finset.strong_induction_on`): if no permutation fits inside `B` the fibre is empty at every level
  (Hall), hence zero; otherwise fix `σ` and apply `isPolyDegLe_of_recurrence_succ`, the sum running
  over strict subsets.

Total so far: **1037 lines** across the five files, no `sorry`, no `axiom`
(`#print axioms` on the payoff theorem returns exactly `propext, Classical.choice, Quot.sound`).

`examples/magic-squares/spencer/Aggregate.lean` (142 lines, clean) then does the two aggregations
S4a/S4b, i.e. **the bridge to the platform's own counting function**:

* `isSemiMagic_iff_lineSums` — the platform's `IsSemiMagic` is verbatim `LineSums`;
* `matBoxLine` — the line-sum-`t` part of the box, as a *named* `noncomputable def` (a bare
  `Finset.filter` may not appear in a theorem's *type*: it would need a `DecidablePred` instance
  before any proof body runs — the same reason `matFiber` and `semiMagicSquares` are defs);
* `card_matBoxLine` — `#(matBoxLine n t) = semiMagicCount n t`, via `Finset.filter_map` (the box is
  `univ` transported along the entry coercion) + `Finset.card_map` + `Finset.filter_congr`;
* `matFiber_eq_filter_matBoxLine`, `semiMagicCount_eq_sum_matFiber` — the support fibres partition
  the semi-magic squares, by `Finset.card_eq_sum_card_fiberwise` over `matSupport`;
* `exists_poly_comp_X_sub_one` — shifting a polynomial sequence down by one (`p.comp (X - 1)`,
  `natDegree_comp_le` + `natDegree_sub_le`), agreement for `t ≥ 1`;
* **the payoff**

  ```lean
  theorem exists_polynomial_semiMagicCount_pos (n : ℕ) :
      ∃ p : Polynomial ℚ, p.natDegree ≤ n * n ∧
        ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
  ```

  = Spencer's theorem in platform terms, with the crude degree bound and only for `t ≥ 1`.

Step 3 is therefore finished — and with it the whole combinatorial input of the proof — and S4 has
since been closed too.  What remains is step 4 (the degree bound `(n-1)²`, §4.2) and the reciprocity
statement S5; see §5, §6 and §8.

## 4. Two subtleties that the exercise write-up does not mention

Both were found by trying to make the recursion *exact* at the boundary, and both are real.
They are the reason the goal statement is hard, and they should not be papered over.

### 4.1 The value at line sum `0`

The support-set decomposition only sees **positive** line sums: a support set is the support of
some magic square, and the squares of line sum `0` only ever have the empty support.  Run the
recursion naively with the empty support `∅` included and it *breaks*: for `B = ∅` there is no
permutation matrix inside `∅`, so `∅` is a base case, not an instance, and the recursion
`h_B(r) = h_B(r-1) + Σ_C h_C(r-1)` fails at `B = ∅`.

The clean way through — verified by hand for `n = 2` — is to **shift**:

* `g_B(r) := h_B(r+1)` for `B ∈ X` (`X` = supports of *positive*-weight squares only, no `∅`);
* the recursion becomes **homogeneous and valid for all `r ≥ 1`**, with **`r = 0` as its base**:
  `g_B(0) = a_B` (= 1 iff `B` is the support of a permutation matrix), and
* the base case is a *constant* generating function, so the naive partial-fraction lemma
  applies at every step with no exceptional numerator (in power-series language: `H_B = P_B/(1-z)^{k_B+1}`
  with `deg P_B ≤ k_B` throughout — contrast the unshifted version, where `H_∅ = 1` forces the
  sloppy case `deg P ≤ k+1` at the bottom and polynomiality only for `r ≥ 1`).

The machinery then produces a polynomial `q` of degree `≤ D` with `q(r) = H_n(r+1)` for all
`r ≥ 0`.  Hence `p := q(X - 1)` satisfies `p(r) = H_n(r)` for all `r ≥ 1`, and the goal
statement additionally demands `p(0) = H_n(0) = 1`, i.e.

  `q(-1) = 1`.

**This is not bookkeeping.**  Writing `s_B := q_B(-1)`, the recursion gives the triangular system

  `s_B = a_B - Σ_{C ∈ nb(B)} s_C`   (`nb(B) = {C ∈ X : B \ φ(B) ⊆ C ⊊ B}`)

and the requirement is `Σ_{B ∈ X} s_B = 1`.  For `n = 2` (`X = {D₁, D₂, Full}`): `s_{D₁} = s_{D₂} = 1`,
`s_{Full} = -s_{D₂} = -1`, sum `= 1` ✓.  Note that `p(-1) = 0` is exactly
**Ehrhart–Macdonald reciprocity at `-1`**, i.e. the statement that `B_n` has no interior lattice
points for `n ≥ 2`.  So `q(-1) = 1` carries the reciprocity content, not a boundary triviality.

*Consequence for the mission*: the rungs cannot be done in the order they are listed.
`semi_magic_polynomial_exists` (agreement on **all** of `ℕ`) needs 4.1 resolved; the honest
intermediate rung is **agreement for `t ≥ 1`**, which the machinery gives for free.

### 4.2 The exact degree `(n-1)²`
Counting the recursion depth naively: each step of the poset recursion raises the degree by one,
the base is `∅` (degree `0`), and each step adds at least one cell, so the chain length from `∅`
to the full support is at most `n² - n + 1`, giving only

  `deg ≤ n² - n`,

which overshoots the true `(n-1)² = n² - 2n + 1` by `n - 1`.  (They agree for `n = 1, 2`, which
is presumably why the cruder bound survives in informal write-ups.)

The sharp bound needs the rank function

  `ρ(B) := |B| - v(B) + c(B)`   (`v` = vertices touched by the bipartite support graph,
                                 `c` = number of its connected components),

which is the dimension of the face of the Birkhoff polytope defined by `B`.  For a support of a
positive-weight square `v(B) = 2n` always, `ρ(B) = 0` exactly when `B` is a permutation support
(the *vertices* of `B_n`), and `ρ(full) = n² - 2n + 1 = (n-1)²`.  Strict inclusion of *support
sets* strictly increases `ρ` (a nested proper face of a polytope has strictly smaller dimension).
That gives `deg ≤ (n-1)²`.

Careful: `ρ` is **not** monotone for arbitrary inclusions of bipartite graphs — adding an edge
that merges two components leaves `ρ` unchanged.  What rules that case out is precisely the
support-set hypothesis: if adding the edge `e` does not change `ρ`, then `e` is forced to `0` by
the line-sum equations, so the larger set is not the support of any square.  So this step needs a
small amount of real argument, not just a counting of cells.

The matching **lower** bound (`deg ≥ (n-1)²`, needed to turn `≤` into `=`) is a separate
question; the cheapest route is probably an explicit family of `c · t^{(n-1)²}` semi-magic
squares, but that is not costed yet.

> ✅ **S3 lower bound landed 2026-09-19**, in `spencer/Degree.lean` (~375 lines, clean, eighth root
> of the `SpencerRoute` lib).  The family is even more explicit than "`c · t^{(n-1)²}`": for order
> `n + 1` and line sum `(n + 1) * s`, put a free block of `n * n` parameters with
> `c : Fin n → Fin n → Fin (s / n + 1)` on the top-left `n × n` corner and let the line-sum
> conditions fill in the last row, the last column and the corner:
>
> ```
> M p q      = s + c p q          (top-left block)
> M p last   = s - Σ_q c p q      (last column)
> M last q   = s - Σ_p c p q      (last row)
> M last last = s + Σ_{p,q} c p q (corner)
> ```
>
> Every line sums to `n*s + Σc + (s - Σc) = (n+1)*s`; `c p q ≤ s / n` bounds `Σ_q c p q ≤ n*(s/n) ≤ s`
> so all entries are `ℕ`; and `c p q = M p q - s` inverts the construction, so it is injective and
>
> ```lean
> theorem semiMagicCount_ge_family (n s : ℕ) (hn : 1 ≤ n) :
>     (s / n + 1) ^ (n * n) ≤ semiMagicCount (n + 1) ((n + 1) * s)
> ```
>
> Growth like `s ^ ((n-1)²)` then forces the degree, through a lemma that needs no analysis:
>
> ```lean
> theorem le_natDegree_of_lowerBound {p : Polynomial ℚ} {d : ℕ} {A : ℚ} (hA : 1 ≤ A)
>     (h : ∀ s : ℕ, 1 ≤ s → (s : ℚ) ^ d ≤ p.eval (A * (s : ℚ))) : d ≤ p.natDegree
> ```
>
> `by_contra d ≤ p.natDegree`; at `x ≥ 1`, `p.eval x ≤ B * x ^ e` where `B = Σ |coeff|` and
> `e = p.natDegree` (`eval_le_mul_pow`, from `eval_eq_sum_range` + `Finset.sum_le_sum`); for `e < d`
> and `s` large, `s ^ d = s ^ (d - e) * s ^ e ≥ s * s ^ e` while the hypothesis gives
> `s ^ d ≤ p.eval (A * s) ≤ B * A ^ e * s ^ e`, so cancelling `s ^ e > 0` yields `s ≤ B * A ^ e`,
> contradicting the choice of `s` (`exists_nat_gt`).  Pure `ℕ`/`ℚ` arithmetic — deliberately no
> asymptotics, since none is needed.
>
> Payoff (note the signature is now character-for-character the platform's
> `semi_magic_polynomial_exists`, apart from the trailing `1 ≤ t`):
>
> ```lean
> theorem exists_polynomial_semiMagicCount_degree_eq (n : ℕ) (hn : 1 ≤ n) :
>     ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧
>       ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
> ```
>
> `#print axioms` on all three new declarations → only `propext, Classical.choice, Quot.sound`.
> Step 4 is therefore **finished**, in both directions; §5's table and §8 record what is left
> overall (only S5).

> ✅ **S3 upper bound landed 2026-09-19.**  Done in `spencer/Rank.lean` + `spencer/Sharp.lean`,
> exactly along the "zero-line-sum space" disguise of `ρ` sketched above — no graphs, no
> vertices, no components.  Highlights:
>
> * `rankB B := dim {M : line sums 0, supp M ⊆ B}` (`Rank.lean`); `rankB_univ : rankB univ = (n-1)²`
>   by rank–nullity on the line-sum map, whose range is the `Σrow = Σcol` hyperplane of dimension
>   `2n - 1` (surjectivity by the explicit transportation matrix
>   `M i j = (a (inl i) + a (inr j) - d/n)/n`, `d = Σcol a`);
> * the strictness input `rankB C < rankB B` for candidates `C ⊂ B` with `φ(τ) ⊆ C` — proved by
>   the **escape lemma** `exists_zeroLine_touching`: if `e ∈ B \ C` were forced to zero, duality
>   (`LinearMap.range_dualMap_eq_dualAnnihilator_ker`) would give `u, v` with `u i + v j = [ij = e]`
>   on `B`; summing over the `τ`-cells (all in `C`) gives `Σu + Σv = 0`, summing over the
>   `σ`-cells (exactly one equals `e`, since `e ∈ B \ C ⊆ φ(σ)`) gives `Σu + Σv = 1`.
>   ⚠️ Both hypotheses are needed: the naive statement "`φ(τ) ⊆ C ⊆ B`, `e ∈ B \ C` ⇒ strict" is
>   **false** (counterexample `B = φ(id) ∪ {bridge cell}`, `C = φ(id)`, `rankB B = rankB C = 0`);
>   what rules the degenerate case out is precisely the candidate constraint `B \ φ(σ) ⊆ C`.
> * `isPolyDegLe_gB_sharp (n) (B) : IsPolyDegLe (rankB B) (gB n B)` (`Sharp.lean`) — same
>   strong-induction skeleton as `isPolyDegLe_gB`, with each candidate split into
>   has-permutation (strict rank bound) / no-permutation (counts vanish, Hall);
> * payoff: `exists_polynomial_semiMagicCount_sharp (n) : ∃ p, p.natDegree ≤ (n-1)² ∧ ∀ t ≥ 1,
>   p.eval t = semiMagicCount n t` — new declaration, published statements untouched.
>   `#print axioms` on both: only `propext, Classical.choice, Quot.sound`.

## 5. Plan

| rung | content | state |
|---|---|---|
| S1 | discrete antiderivative + Spencer step (steps 1–2) | **done**, `spencer/Spencer.lean` |
| S2a | Hall: a positive-weight line-sum matrix contains a permutation | **done**, `spencer/HallSupport.lean` |
| S2b | the split `T ↦ T - P` and its support behaviour | **done**, `spencer/SupportSplit.lean` |
| S2c | cardinal assembly: fibres `{supp = C}`, `B \ φ ⊆ C ⊆ B`, partition the level-`s` fibre (completes step 3) | **done**, `card_matFiber_split` + `card_matFiber_recurrence` in `spencer/SupportSplit.lean` |
| S2d | cancellation of the ambient bound; Hall choice of `σ_B` for a support set `B`; well-founded induction on `B.card` + `isPolyDegLe_of_recurrence_succ` ⇒ `g_B` polynomial | **done**, `spencer/Recursion.lean` (`isPolyDegLe_gB`) |
| S3 | degree bound via `ρ` (step 4, sharp version) **and** the matching lower bound | **done, both directions** 2026-09-19 — upper bound `spencer/Rank.lean` + `spencer/Sharp.lean`; lower bound `spencer/Degree.lean`, giving the **exact** degree `(n-1)²` for `t ≥ 1` (`exists_polynomial_semiMagicCount_degree_eq`) |
| S4a | the cardinality bridge: `semiMagicCount n t = Σ_{B ⊆ univ} #(matFiber n t t B)`, i.e. `matBox n t` is `univ` transported along `↑` | **done**, `spencer/Aggregate.lean` (`semiMagicCount_eq_sum_matFiber`) |
| S4b | `IsPolyDegLe` is closed under the shift `r ↦ r + 1` and under sums over a finite set, so `t ↦ semiMagicCount n t` agrees with a polynomial for `t ≥ 1` | **done**, `spencer/Aggregate.lean` (`exists_polynomial_semiMagicCount_pos`, degree `≤ n * n`) |
| S5 | `q(-1) = 1` (= reciprocity at −1) | the hard one; see §4.1 and **`S5-NOTES.md`** — 2026-09-20: reduced to exactly (A) `q_B(−1) = (−1)^rankB B` on supports + (B) `Σ_B(−1)^rankB B = 1`, both verified numerically for `n ≤ 4`; the reduction itself is now machine-checked in
`spencer/S5.lean` (§8.5) |

Suggested ordering given §4.1: **S2 → S3 → S4, then publish the `t ≥ 1` statement as a new
node**, and treat S5 as its own research problem.  `semi_magic_count_four` (`n = 4`) has the
same two subtleties plus a concrete interpolation problem, so it is *not* an easier substitute.

Status 2026-09-19: **S1, S2a–d, S3 (both directions) and S4a–b are all closed.**  The whole
combinatorial core of Spencer's proof plus the exact degree bound now exist locally, with no
`sorry` and no `axiom`; **S5 is the only rung left**, and it is a genuinely separate research
problem (Ehrhart–Macdonald reciprocity at `-1`).

## 6. Fallback if S5 does not yield

Publish `TaoFivePrimes`-style: a new node in the mission,

```lean
theorem semi_magic_polynomial_exists_pos (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ (n - 1) ^ 2 ∧ ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
```

attached to the live mission by a milestone carrying its `theorem_id` (captain-only; the user is
the captain of these missions).  That is a real theorem, it is exactly "Spencer's theorem", and
it leaves the reciprocity-flavoured residue visible as a separate obligation rather than
silently assuming it.

✅ **This node now exists as a proved local theorem** (2026-09-19, `spencer/Aggregate.lean`):

```lean
theorem exists_polynomial_semiMagicCount_pos (n : ℕ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ n * n ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
```

Two deviations from the text above, both deliberate: no `hn : 1 ≤ n` (the statement is fine for
`n = 0`, where the count is the constant `1` and `0 ≤ 0`), and the degree bound is the crude
`n * n` rather than `(n-1)²` — sharpening it is rung S3 and will require a **new** declaration
rather than an edit, so that the published statement is never silently weakened.  Publishing is
still blocked: mission V's proposal is `In review`, so there is no mission to attach the node to.

✅ **The sharp sibling now exists as a proved local theorem** (2026-09-19, `spencer/Sharp.lean`;
see §4.2 for the proof outline):

```lean
theorem exists_polynomial_semiMagicCount_sharp (n : ℕ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ (n - 1) ^ 2 ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
```

This is the theorem §6 recommended publishing.  Both nodes could go up together once mission V is
live — **and mission V is live now** (`e06131f8-1bf5-47c4-b8f4-507f107269e0`; proposal `3a8476fd`
flipped to `Reviewed` at `2026-09-19T15:01:27Z`), so publishing is a captain action away.

✅ **And the exact-degree sibling too** (2026-09-19, `spencer/Degree.lean`) — the strongest of the
three local nodes, and the one that differs from the published goal only by the hypothesis `1 ≤ t`:

```lean
theorem exists_polynomial_semiMagicCount_degree_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
```

⚠️ **Do not publish this as the goal node.**  The published `semi_magic_polynomial_exists`
quantifies over **all** of `ℕ` (`∀ t : ℕ, …`, verified from
`GET /theorems/3dc34529-feed-4b21-bd4f-443097422b63`), so `degree_eq` is a sibling, not a solution.
Publishing it as the goal would be false advertising; publish it as its own node under the same
milestone (or a new one), and leave the goal `Open` until S5 lands.

## 7. Implementation notes for S2b (found the hard way, 2026-09-19)

### 7.1 The ambient-bound bookkeeping — **as finally solved**

`SupportSplit.lean` now contains the solution, and it is *not* the one first sketched here.  The
platform's `semiMagicSquares n t : Finset (Square n (Fin (t+1)))` bounds the entries because the
line sum is `t`, and that bound makes the fibre finite — but it also makes the level-`s` and the
level-`(s-1)` fibres two *different types*, so no `card_bij` can compare them.  Worse, `Fin`'s
subtraction **wraps around** (`x - y = (x - y) % n`), so transporting `T - P` across levels is not
even a truncation.

What works: describe a fibre as a finset of **`ℕ`-valued** matrices cut out by an explicit bound
*condition*, and manufacture finiteness once, from the `Fin`-valued box:

  `matBox n s := (Finset.univ : Finset (Square n (Fin (s+1)))).map ⟨fun M i j => (M i j : ℕ), …⟩`

with `mem_matBox : M ∈ matBox n s ↔ ∀ i j, M i j ≤ s`.  Then the two levels live in the same type,
and

  `matFiber n m s B := (matBox n m).filter (fun M => LineSums M s ∧ matSupport M = B)`

carries *both* the ambient bound `m` and the line sum `s` as ordinary data.  The recurrence is

  `(matFiber n s s B).card = (matFiber n s (s-1) B).card + Σ_{C ∈ nb(B)} (matFiber n s (s-1) C).card`

(`card_matFiber_recurrence`), with `nb(B) := (fiberCandidates B φ).erase B` and
`fiberCandidates B φ := B.powerset.filter (fun C => B \ φ ⊆ C)`.

The cancellation that was still owed here is `matFiber_eq_of_le` in `Recursion.lean`: line sums `s`
already force every entry to be `≤ s`, so the ambient bound `m` is redundant as soon as `s ≤ m`.
With `h_B s := (matFiber n s s B).card` the recurrence becomes, for `s ≥ 0`,

  `h_B(s+1) = h_B(s) + Σ_{C ∈ nb(B)} h_C(s)`

(`card_matFiber_recurrence_succ`, where `nb(B) := nbSupp B φ`).  Setting `g_B r := h_B (r+1)` this is
`g_B (r+1) = g_B r + Σ_C g_C r` — the hypothesis of `isPolyDegLe_of_recurrence_succ`, with the
constant `g_B 0 = a_B` as its base.  Note that `σ` is a *parameter* of the recurrence: it is chosen
once per support set `B` and serves every line sum, because any `σ` with `φ(σ) ⊆ B = supp T` already
satisfies the positivity hypothesis of the split for that `T`.

### 7.2 Mathlib names that actually work (2026-09-19, this pin)

Verified by compiling `examples/magic-squares/spencer/SupportSplit.lean`:

| wanted | works | does **not** work |
|---|---|---|
| `(A + B) i j = A i j + B i j` | `Matrix.add_apply A B i j` | — |
| `(A - B) i j = A i j - B i j` | `Matrix.sub_apply A B i j` | — |
| `∑ x, (if a = x then f x else 0) = f a` | `Finset.sum_ite_eq` | `Finset.sum_ite_eq'` (that one is the `if x = a` form) |
| `∑ x, (f x - g x) = ∑ x, f x - ∑ x, g x` | — | `Finset.sum_sub_distrib` did not match the `∑ x,` (univ) form; **go through `Finset.sum_add_distrib` instead** (`T = (T - P) + P`, then `Nat.sub_add_cancel`) |
| permutation matrices | own `permMatrix σ i j = if σ i = j then 1 else 0` | — (Mathlib has `PEquiv.toMatrix` in `Analysis/Convex/Birkhoff.lean`, possibly a cheaper route; not explored) |

Also: `rw` inside sums is brittle because the univ-sum `∑ x, f x` and the two-argument
`∑ x ∈ s, f x` are only definitionally equal; prefer `have`-bound local rewrite rules and
`Finset.sum_congr`, or reformulate to avoid the sum identity entirely.

### 7.3 What `SupportSplit.lean` now gives

The file (401 lines, clean) contains bricks 4, 5 and 6:

* the forward map and its exact support behaviour (§3 above);
* `matBox`, `matFiber`, `fiberCandidates` and the auxiliary identities needed to move between
  them (`le_of_rowSum`, `matBox_sub_permMatrix`, `mem_matBox_add_permMatrix`,
  `sum_add_permMatrix`, `permMatrix_le_one`, `union_eq_of_subset`,
  `mem_matSupport_permMatrix_self`);
* **`card_matFiber_split`** — `Finset.card_bij` (with `Finset.card_sigma`) showing that
  `T ↦ T - P` is a bijection from `matFiber n s s B` onto
  `(fiberCandidates B φ).sigma (fun C => matFiber n s (s-1) C)`;
* **`card_matFiber_recurrence`** — splitting off the term `C = B` with `Finset.sum_erase_add`,
  which yields the recurrence of §7.1 in exactly the shape `isPolyDegLe_of_recurrence` wants.

Note that `C` need *not* be assumed to be a support set: the fibres of non-supports are simply
empty, which is why the sum can be taken over `B.powerset` and why the set `X` of support sets
never has to be materialised.

## 8. How to build, and exactly what is left

### 8.1 Building

The files import each other, so they are a real Lake library (2026-09-19, added alongside
`RosserLcmBlocks` in `lakefile.lean`); since Brick 12 landed the lib has **nine** roots
(`Spencer, HallSupport, SupportSplit, Recursion, Aggregate, Rank, Sharp, Degree, S5`):

```
lake build SpencerRoute          # builds all nine, ~2-3 min cold, one module ~30 s warm
```

The library is **not** a default target, so a plain `lake build` is unaffected.  Module names inside
imports carry guillemets for the hyphenated directory, e.g.
`import examples.«magic-squares».spencer.SupportSplit`.  Because `Definitions` is itself a lean_lib,
`Aggregate.lean` can `import Definitions.Def_MagicSquares` and speak the platform's own vocabulary
(`semiMagicCount`, `IsSemiMagic`) instead of re-stating it.

`lakefile.lean` is tracked *and* matches no ignore rule (verified 2026-09-19: `git ls-files` lists
it, `git check-ignore` says nothing), so a plain `git add lakefile.lean` is enough — an older note
here claimed `-f` was needed, which is not true.  To print a statement (and its axiom dependencies)
without a build target, use a scratch file plus `lake env lean`:

```lean
-- tmp/check_aggregate.lean
import examples.«magic-squares».spencer.Aggregate
#print MagicSquaresSpencer.exists_polynomial_semiMagicCount_pos
#print axioms MagicSquaresSpencer.exists_polynomial_semiMagicCount_pos
```

### 8.2 S4a — the cardinality bridge to `semiMagicCount` — **done**

`Definitions/Def_MagicSquares.lean` has

```lean
def semiMagicSquares (n t : ℕ) : Finset (Square n (Fin (t + 1))) :=
  Finset.univ.filter fun M => IsSemiMagic (fun i j => (M i j : ℕ)) t
def semiMagicCount (n t : ℕ) : ℕ := (semiMagicSquares n t).card
```

and `matBox n t` is by construction the *image* of `Finset.univ : Finset (Square n (Fin (t+1)))`
under `↑` (an injective map), so `matBox n t` is `univ` transported along `↑`.  Accordingly:

* `IsSemiMagic M t ↔ LineSums M t` for ℕ-valued `M` is literally `Iff.rfl`-true, as guessed —
  `rowSum`/`colSum` *are* the `∑ j`/`∑ i`;
* the transport is `Finset.filter_map` + `Finset.card_map` + `Finset.filter_congr`
  (`card_matBoxLine`);
* the partition by support is `Finset.card_eq_sum_card_fiberwise` over `matSupport`
  (`semiMagicCount_eq_sum_matFiber`), which needs the sums to run over `univ.powerset` — all `n²`
  cells — because non-supports contribute `0`.

⚠️ One gotcha the recipe above did not anticipate: a bare `Finset.filter (fun M => LineSums M t)`
may **not** appear in a theorem's *type* (the line-sum part of the box had to become the named def
`matBoxLine`), because the type is elaborated before any `classical` in the proof body.

### 8.3 S4b — from `gB` to `semiMagicCount` — **done**

For `t ≥ 1`, S4a plus the definition of `gB` give

```lean
(semiMagicCount n t : ℚ) = ∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, gB n B (t - 1)
```

so the promised polynomial is the shift by one of `r ↦ Σ_B gB n B r`.  Two ingredients were needed,
both as predicted:

* `exists_poly_comp_X_sub_one` : `IsPolyDegLe K b → ∃ p, p.natDegree ≤ K ∧ ∀ t, 1 ≤ t → p.eval t = b (t - 1)`,
  by `p.comp (X - C 1)` (`natDegree_comp_le` + `natDegree_sub_le`).  Note it is `X - 1`, not `X + 1`:
  the recursion is indexed by the *predecessor* of the line sum;
* the uniform degree bound: `isPolyDegLe_sum` needs *one* `K` for all `B ∈ univ.powerset`, supplied
  by `isPolyDegLe_mono` from `B.card ≤ n * n`.

Result: `exists_polynomial_semiMagicCount_pos` of §6, degree `≤ n * n`.  §4.1 is the reason the
statement cannot cover `t = 0`; the sharp `(n-1)²` (S3 / §4.2) is independent of S4 and can be
attacked either before or after.

✅ Both sharpenings have since landed — `spencer/Sharp.lean` (degree `≤ (n-1)²`) and
`spencer/Degree.lean` (degree `= (n-1)²`, via the explicit family of §4.2).  The local endpoint is
now `exists_polynomial_semiMagicCount_degree_eq`, still with the `1 ≤ t` restriction; the crude
`exists_polynomial_semiMagicCount_pos` is kept because it is the published `§6` sibling and its
statement must not be edited in place.

### 8.4 Brick 11 — build and verify — **done**

```lean
-- tmp/axiom_check_degree.lean
import examples.«magic-squares».spencer.Degree
#print axioms MagicSquaresSpencer.semiMagicCount_ge_family
#print axioms MagicSquaresSpencer.le_natDegree_of_lowerBound
#print axioms MagicSquaresSpencer.exists_polynomial_semiMagicCount_degree_eq
```

→ all three report `[propext, Classical.choice, Quot.sound]`.  Implementation notes worth keeping,
all of them `simp`/`rw` friction rather than mathematics:

* `lowerBlock` is defined with the branch test `(i : ℕ) = n`, but `Fin.castSucc p`'s value is
  `↑p`; `simp only [lowerBlock]` leaves the `if` unreduced.  The fix is to state the side
  conditions as `¬(((Fin.castSucc p : Fin (n+1)) : ℕ) = n)` and finish with
  `rw [if_neg hi, if_neg hj, blockIdx_castSucc hn p]` (or `if_pos (Fin.val_last n)` for the last
  index).  Four `lowerBlock_*` lemmas, one per block corner.
* `∑ i ∈ u, (a - X i) = u.card * a - ∑ i ∈ u, X i` is **not** in Mathlib in usable form; it is
  proved here by `Finset` induction (`sum_sub_const`), with the insert step needing
  `u.card * a + a = (u.card + 1) * a` handed to `omega` explicitly rather than left to `ring`.
* `Fin.sum_univ_castSucc` (not `sum_univ_succ`) is the split `∑ i, f i = ∑ i, f (i.castSucc) + f (Fin.last n)`
  used for every row/column sum.
* `push_neg` is deprecated in this pin alongside `autoImplicit false`; use `push Not`.
* `le_or_lt` / `lt_or_le` are not in scope as bare names in this file — `by_cases hn2 : 1 < n`
  with an explicit `n ≤ 1` branch is the rewrite that compiles.

### 8.5 Brick 12 (`S5.lean`) — the S5 reduction, machine-checked — **done** 2026-09-20

`spencer/S5.lean` turns `S5-NOTES.md` §3 into Lean.  New declarations:

| declaration | what it says |
|---|---|
| `qB n B`, `qB_natDegree`, `qB_eval` | the polynomial with `qB n B r = #(line-sum-`(r+1)` fibre at `B`)`, degree `≤ #B` |
| `sB`, `sB_eq` | `sB n B := qB n B (-1)` — the number S5 is about |
| `nbOf n B` | the split's neighbour set, `∅` when no permutation fits inside `B` |
| `gB_succ` | `gB n B (r+1) = gB n B r + Σ_{C ∈ nbOf n B} gB n C r`, at **every** `B` |
| `qB_rec` | `qB (X+1) - qB = Σ_{C ∈ nbOf n B} qB C`, an identity in `ℚ[X]` |
| `sB_rec` | `sB n B = #(level-1 fibre at B) - Σ_{C ∈ nbOf n B} sB n C` — no polynomial left |
| `IsSupport`, `supportSet` | "support of a square of positive line sum", as a finset |
| `sB_eq_zero_of_not_isSupport` | non-supports contribute `0` |
| `ReciprocityAtNegOne`, `FaceLatticeEuler` | (A) and (B) of `S5-NOTES.md` §3, as `Prop`s |
| `sum_sB_eq_one_of` | (A) + (B) ⟹ `Σ_B sB n B = 1` |
| `exists_polynomial_semiMagicCount_of_sum_sB` | `Σ_B sB n B = 1` ⟹ the count is polynomial on **all** of `ℕ` |
| `exists_polynomial_semiMagicCount_degLe_of_sum_sB` | the same, with `natDegree ≤ (n-1)^2` kept |

The last two are the machine-checked form of "the only missing inputs are (A) and (B)": the
polynomial is `qAll n := (Σ_B qB n B).comp (X - 1)`, `qAll_eval_pos` gives agreement for `t ≥ 1`
without any new input, and `qAll_eval_zero` identifies the value at `t = 0` with `Σ_B sB n B`.
Together with `degree_eq` this says: **`Σ_B sB n B = 1` ⟹ the mission's goal.**

No `sorry`, no `axiom`: all new theorems report `[propext, Classical.choice, Quot.sound]`
(`tmp/axiom_check_s5.lean`); `lake build SpencerRoute` is green (`Built …S5 (23s)`).

Implementation notes (all `simp`/`rw` friction; they will recur):

* **A polynomial vanishing on `ℕ` is zero** (`poly_eq_zero_of_nat_eval_eq_zero`, via
  `Polynomial.eq_zero_of_infinite_isRoot` + `Set.infinite_range_of_injective Nat.cast_injective`);
  the positive-integer version multiplies by `X` and uses `Polynomial.X_ne_zero`.  This is the only
  `ℚ[X]`-specific input of the brick, and it is what turns a recurrence in `t : ℕ` into a
  polynomial identity — i.e. what makes evaluating at `-1` legitimate at all.
* `(0 : ℚ)` and `((0 : ℕ) : ℚ)` are **not** interchangeable for `rw`.  Three rewrites failed on
  this; either state the lemma with the same cast shape as the call site (`qAll_eval_zero` is
  stated at `((0 : ℕ) : ℚ)` for exactly this reason) or insert
  `have hc : (0 : ℚ) = ((0 : ℕ) : ℚ) := by norm_num` first.
* `Sharp.lean` **already had** `gB_eq_zero_of_no_perm`, in the shape `(∀ σ, ¬ φ ⊆ B)` rather than
  `¬ ∃ σ, φ ⊆ B`.  Same statement, different term: reuse it and pass `fun σ hσ => h ⟨σ, hσ⟩`.
* `semiMagicCount` lives in the `MagicSquares` namespace — `open MagicSquares` is required (every
  other brick that mentions it has it).
* unfolding a `by classical exact …` definition (`supportSet`) needs `classical` **in the proof
  that unfolds it**, or `DecidablePred (IsSupport n)` cannot be synthesised.
* `(A - B - C).eval x` needs `eval_sub` twice (left-associated `-`); `simp only [Polynomial.eval_sub,
  …]` handles both matches in one pass, a `rw` list may not.
