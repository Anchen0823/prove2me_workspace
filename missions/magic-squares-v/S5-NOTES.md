# S5 — the value at line sum `0` (`q(-1) = 1`)

> **Superseded on 2026-09-20:** the zero-value obstruction is now closed locally by a different, closed-support induction. `ClosedPolynomial.lean` proves polynomiality on all natural line sums and `sum_sB_eq_one`, without proving either individual input (A) or (B). The earlier assessment that Euler/reciprocity or triangulation was a necessary next step was too restrictive. See [CLOSED-SUPPORT.md](CLOSED-SUPPORT.md) and the latest [status](status.md). Historical analysis below is retained.


Working notes, 2026-09-20.  Read after `SPENCER-ROUTE.md` §4.1 and §5.

## 1. What is left, stated exactly

The Spencer route produces, for every `n ≥ 1`,

```lean
exists_polynomial_semiMagicCount_degree_eq (n) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧ ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
```

The published goal `semi_magic_polynomial_exists` is the same statement with the hypothesis
`1 ≤ t` **removed**.  So the whole remaining gap is the single value at `t = 0`:

> **S5.**  Let `q ∈ ℚ[X]` be the polynomial of degree `D := (n-1)²` with `q(r) = H_n(r+1)` for all
> `r ∈ ℕ` (take `q := p.comp (X + 1)` from `exists_polynomial_semiMagicCount_degree_eq`; the shift is
> non-constant, so the degree is preserved).  Then `q(-1) = H_n(0) = 1`.

Nothing else is missing: given `q(-1) = 1`, `p := q.comp (X - 1)` has `p(0) = 1 = H_n(0)` and
`p(t) = H_n(t)` for `t ≥ 1` already.

## 2. Where the value at `0` disappears

The support recursion is only valid for **positive** line sums.  With

* `h_B(s) := (matFiber n s s B).card`  (squares of line sum `s` supported exactly on `B`),
* `g_B(r) := h_B(r+1)`,  `q_B` = the polynomial with `q_B.eval r = g_B r` for all `r` (degree `= rankB B`),

the recurrences are (`nb(B)` as in `Recursion.lean`)

```
h_B(s+1) = h_B(s) + Σ_{C ∈ nb(B)} h_C(s)          (valid for s ≥ 0)
g_B(r+1) = g_B(r) + Σ_{C ∈ nb(B)} g_C(r)          (valid for r ≥ 0)
```

The reason `s = 0` is not covered is *the empty support*: for `n ≥ 1`, `h_∅(s) = [s = 0]`, so
`h_∅` is not a polynomial, and `h_∅` occurs on the right-hand side exactly when `B` is a
permutation support (`φ_B = B`).  Summing over all non-empty `B` therefore gives a polynomial that
agrees with `H_n` on `t ≥ 1` only; the information at the single point `s = 0` is not visible.
Concretely, with `q := Σ_{B ≠ ∅} q_B` and `p := q.comp (X - 1)`:

```
H_n(t) = p(t)  for t ≥ 1,        but p(0) = q(-1) is not pinned.
```

## 3. Reduction of S5 to two statements

Every `B` in the recursion carries a chosen permutation support `φ_B ⊆ B` and

```
nb(B) = {C : B \ φ_B ⊆ C ⊊ B},        a_B := h_B(1) = 1 if B is a permutation support, else 0.
```

Evaluating the polynomial identity `q_B(X+1) − q_B(X) = Σ_{C ∈ nb(B)} q_C(X)` at `X = −1` gives,
with `s_B := q_B(−1)`,

```
s_B = a_B − Σ_{C ∈ nb(B)} s_C        (B containing a permutation support)
s_B = 0                              (B containing none, by Hall: the fibre is empty at every level)
s_∅ = 0                              (n ≥ 1)
```

and S5 is exactly

```
S5   ⟺   Σ_{B ≠ ∅} s_B = 1 .
```

Two statements feed into it:

> **(A)**  For every **support** set `B` (a set of cells that is the support of some semi-magic
> square): `q_B(−1) = (−1)^(rankB B)`, where `rankB B = dim {M : line sums 0, supp M ⊆ B}` is the
> dimension of the corresponding face of the Birkhoff polytope.
>
> **(B)**  `Σ_{∅ ≠ B support} (−1)^(rankB B) = 1`.

(A) is Ehrhart–Macdonald reciprocity at `−1`: `q_B(r) = L_{F_B}(r+1)` is the interior Ehrhart
polynomial of the face `F_B`, so `q_B(−1) = L_{F_B°}(0)`, and reciprocity at `0` says
`L_{P°}(0) = (−1)^(dim P)`.  Equivalently: the face has no interior lattice points at scale `1`
and its Ehrhart numerator has constant term `1`.

(B) is not a counting identity at all: supports of `B_n` biject onto the non-empty faces of the
Birkhoff polytope `B_n` with `rankB ↔ dim`, so (B) is

```
Σ_{∅ ≠ F face of B_n} (−1)^(dim F) = 1 ,
```

which for a `d`-polytope is exactly Euler's formula `Σ_{k=0}^{d−1}(−1)^k f_k = 1 + (−1)^(d−1)`
combined with `f_d = 1`.  It holds for **every** polytope, not just `B_n`, and it is the one
statement in sight that has no Ehrhart theory in it at all.

## 4. Numerical verification (exact arithmetic, `tmp/s5_probe.py`, `tmp/s5_probe4.py`)

For each `n`, all semi-magic `n × n` squares with line sums `s` were enumerated (rows-with-prescribed-
sum enumeration, `Fraction` arithmetic, no floating point) — `s = 1 … 6` for `n = 2, 3` and
`s = 1 … 11` for `n = 4`, enough to interpolate every `q_B` (degree `rankB B ≤ 9`) and then to check
the degree on further levels — bucketed by exact support `B`, and for every support that occurs

* `rankB B` was computed by Gaussian elimination over `ℚ` on the line-sum system restricted to `B`;
* `q_B` was reconstructed by Newton/Lagrange extrapolation from `g_B(0) … g_B(rankB B)`;
* the degree `rankB B` was **checked** against the remaining computed levels `r > rankB B`.

| `n` | distinct supports | `q_B(−1) = (−1)^rankB B` | `deg g_B ≤ rankB B` | `Σ_B q_B(−1)` | `Σ_B (−1)^rankB B` |
|---|---|---|---|---|---|
| 2 | 3 | 3 / 3 | 3 / 3 | **1** | **1** |
| 3 | 49 | 49 / 49 | 49 / 49 | **1** | **1** |
| 4 | 7443 | 7443 / 7443 | 7443 / 7443 | **1** | **1** |

So (A) and (B) both hold for `n ≤ 4`, and `Σ_B s_B = 1` holds for `n ≤ 4`.  Note the two sums are
computed **independently**: the `q_B(−1)` column is extrapolated from the fibre counts alone (no use
of (A) or (B)), so the middle column verifies **S5 itself** for `n ≤ 4`, while the last column
verifies (B).  The `n = 4` run also
reproduces the published counts `H_4(s)` for `s = 1 … 11`
(`1, 24, 282, 2008, 10147, 40176, 132724, 381424, 981541, 2309384, 5045326, 10356424`), which agree
with Beck–Pixton's `H_4` polynomial — an independent check of the enumeration itself.

⚠️ Note what this is and is not: this is **numerical evidence**, not a proof.  For `n = 5` the same
probe is out of reach (the level-`s` enumeration grows like the count itself), and no finite number
of cases would settle a statement uniform in `n` in any case.

## 5. Equivalent formulations of S5 (all verified to be equivalent, none easier)

* `p(0) = 1` for the degree-`D` polynomial agreeing with `H_n` on `t ≥ 1`.
* `Σ_{j=1}^{D+1} (−1)^(j−1) C(D+1, j) H_n(j) = 1`  (Newton series for `q` at `−1`, hockey stick).
* Writing `S(z) := Σ_{t≥0} H_n(t) z^t`:  `S(z) = A(z)/(1−z)^(D+1)` with `deg A ≤ D + 1`, and the
  top coefficient satisfies `[z^(D+1)] A = 0` — equivalently `Σ_{∅≠B} (−1)^(rankB B) u_B = 1`,
  where `u_B` is the leading coefficient of the numerator of `Σ_{r≥0} q_B(r) z^r`.
* `Δ^(D+1) H_n(0) = 0`: the sequence `t ↦ H_n(t)` is polynomial on all of `ℕ` — i.e. exactly the
  statement that `B_n` is a lattice polytope with Ehrhart polynomial of degree `(n-1)²`, which is
  what Ehrhart's theorem gives for free and what the elementary route has to redo.

## 6. Status and options

S5 is **not** a cheap corollary, and it is not a bookkeeping gap.  Either input is a real theorem:

| route | what must be formalised | cost |
|---|---|---|
| (A) | Ehrhart–Macdonald reciprocity for the face `F_B` (Mathlib has **no** Ehrhart theory) | big |
| (B) | `Σ_{nonempty faces F of B_n} (−1)^dim F = 1` — Euler's formula for the boundary of a polytope, via a shelling or a triangulation | big, but polytope-general, so it is reusable |
| both | the recursion of §3 (polynomial identity ⇒ `s_B` system) | small-ish, purely formal |

Options, in the order I would try them:

1. **Leave the goal `Open`.**  Three sibling nodes are already published
   (`exists_polynomial_semiMagicCount_pos`, `…_sharp`, `…_degree_eq`), the last of which differs
   from the goal only by `1 ≤ t`.  This is the honest state of the art of the elementary route.
2. **Do §3 in Lean** (small): replaces S5 by the purely combinatorial `Σ_B s_B = 1`, no polynomials
   left.  Worth doing because it makes the obstruction exactly (A)+(B), and because (B) is
   polytope-general, so it is not wasted effort even if the mission's goal never closes this way.
3. **Attack (B) first.**  It is the half that has nothing to do with reciprocity, it is true for
   every polytope, and the `n = 4` data (7443 supports, clean cancellation) shows the identity is
   robust rather than a small-`n` accident.  A shelling argument for the Birkhoff polytope is still
   a project; a *purely combinatorial* proof of `Σ_F(−1)^dim F = 1` for this face lattice would be
   the actual contribution.
4. **Attack (A) last.**  It is reciprocity, i.e. interior lattice points, and the mission's other
   two open rungs (`semi_magic_reciprocity`, `semi_magic_vanishing`) are the same theorem in
   different clothes — so (A) is *not* a detour, it closes three rungs at once.  All the more
   reason not to attempt it as a side quest.

**Status 2026-09-20 (same day, later).**  Option 2 is **done**: `examples/magic-squares/spencer/S5.lean`
(Brick 12) makes §3 machine-checked.  See §7.

## 7. What is now machine-checked (Brick 12, `spencer/S5.lean`)

§1–3 above was a derivation on paper.  The following are now Lean theorems, no `sorry`, no `axiom`
beyond `[propext, Classical.choice, Quot.sound]`, and `lake build SpencerRoute` is green
(implementation pitfalls: `SPENCER-ROUTE.md` §8.5):

* `qB n B` with `qB_eval : (qB n B).eval r = #(fibre of line sum r+1 at B)`;
* `nbOf n B` — the split's neighbour set, with the convention `nbOf n B = ∅` when no permutation
  fits inside `B`.  That convention is what makes `gB_succ`
  (`gB n B (r+1) = gB n B r + Σ_{C ∈ nbOf n B} gB n C r`) true at **every** `B`, not only at the
  supports — the "no permutation" case is handled by Sharp's `gB_eq_zero_of_no_perm`;
* `qB_rec`, the polynomial identity `qB (X+1) − qB = Σ_{C ∈ nbOf n B} qB C`.  Its proof is where
  the "polynomial vanishing on `ℕ` is zero" lemma is used, and that lemma is the *entire* reason
  evaluating at `X = −1` is legitimate;
* `sB n B := qB n B (−1)` and `sB_rec : sB n B = #(level-1 fibre at B) − Σ_C sB n C` — §3's
  recursion, with no polynomial left;
* `IsSupport n B` / `supportSet n` (support of a square of *positive* line sum) and
  `sB_eq_zero_of_not_isSupport`;
* `ReciprocityAtNegOne n` (this is **(A)**) and `FaceLatticeEuler n` (this is **(B)**) as `Prop`s;
* `sum_sB_eq_one_of : (A) → (B) → Σ_B sB n B = 1`;
* `exists_polynomial_semiMagicCount_of_sum_sB` and `…_degLe_of_sum_sB`: `Σ_B sB n B = 1` implies
  the count agrees with a polynomial on **all** of `ℕ`, the second with `natDegree ≤ (n−1)²` kept.
  With `Degree.lean`'s `exists_polynomial_semiMagicCount_degree_eq` this is: **S5 ⟹ the goal.**

So the mission's goal now follows from the *single* numerical identity `Σ_B sB n B = 1`, which the
brick does **not** prove.  (A) and (B) remain exactly as stated in §3 and are still the whole
content of S5.

## 7.1 (A)+(B) is not the only route: S5 *is* Ehrhart's theorem for `B_n`

Worth recording, because it changes what a future attempt should aim at:

> `H_n(t) = #(t·B_n ∩ ℤ^{n×n})` — the line-sum-`t` semi-magic squares *are* the lattice points of
> the `t`-th dilate of the Birkhoff polytope, which has integral vertices (the permutation
> matrices).  So `p(0) = 1` is exactly **Ehrhart's theorem** for `B_n`: a lattice polytope's
> counting function is a polynomial in `t` for all `t ∈ ℕ`, of degree `dim`, with value `1` at `0`.

Note the asymmetry: `(A)` (reciprocity) is *stronger* than needed, and `(B)` alone is not enough.

There is an elementary route to Ehrhart's theorem that uses **neither**: triangulate into lattice
simplices and use inclusion–exclusion.  For a `d`-dimensional lattice simplex `Δ` with
`C := cone(Δ × {1})` and fundamental parallelepiped `Π ⊆ C`,

  `L_Δ(t) = Σ_{y ∈ Π ∩ ℤ^{d+1}} binom(t − deg y + d, d)`   for **all** `t ≥ 0`,

because `x ∈ tΔ ∩ ℤ^d` is equivalent to `x = Σ_i (k_i + f_i) v_i` with `k_i ∈ ℕ`,
`0 ≤ f_i < 1`, `Σ k_i + Σ f_i = t`, and the pair (integer part, fractional part) is unique by
affine independence of the `v_i`; the number of `k`-choices is the binomial.  Here `deg y` is the
last coordinate of `y ∈ ℤ^{d+1}`, hence an integer, and `0 ≤ deg y ≤ d` (strictly below `d+1`),
so at `t = 0` every `deg y ≥ 1` term dies and `L_Δ(0) = binom(d,d) = 1` — the value S5 asks for,
for free.  For a general lattice polytope, take a lattice triangulation `T`, use the *pointwise*
identity `1_P = Σ_{∅≠S⊆T} (−1)^{|S|+1} 1_{∩S}` (each `∩S` a lattice polytope of dimension `< d`
as soon as `|S| ≥ 2`), and induct on dimension: every term is a polynomial for all `t ≥ 0`, hence
so is `L_P`, and its value at `0` is the alternating sum of `1`s, i.e. `1`.

Check of the binomial formula on a non-unimodular example (done by hand 2026-09-20, the reason to
trust it): `Δ = conv{(0,0),(2,0),(0,2)}`, `d = 2`.  `Π ∩ ℤ³ = {(0,0,0), (1,0,1), (0,1,1), (1,1,1)}`,
so `h*(z) = 1 + 3z` and `Σ_y binom(t − deg y + 2, 2) = binom(t+2,2) + 3 binom(t+1,2) =
2t² + 3t + 1`, which is the true Ehrhart polynomial of that triangle (`L(0)=1, L(1)=6, L(2)=15`).
A sloppier enumeration of `Π` gives `h* = 1 + z` and the wrong answer, so the `f_0 ∈ [0,1)` case
must be kept in the parallelepiped.

So the *alternative* endgame is a **lattice-polytope Ehrhart development in Mathlib** (simplex
binomial count + lattice triangulations + inclusion–exclusion), which would close the goal
directly without (A) or (B).  It is a project — it needs affine independence, the
integer/fractional decomposition, and a triangulation of `B_n` — but it is self-contained, it has
no reciprocity and no face-lattice Euler formula in it, and half of it (the simplex count) is
already verified above.  Keep it as the route to compare against (A)+(B).
