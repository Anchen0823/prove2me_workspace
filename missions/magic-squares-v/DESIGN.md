# Mission V — design (2026-09-19)

Status: **proposal not yet created.** This document is the design; the proposal
(goal theorem + definitions + milestones) is the next action. Direction given by
the user: *order ≥ 4 or general n, and prefer a long path with a big project.*

---

## 1. Chosen target: BCCG Theorem 1 (Ehrhart–Stanley)

> **Theorem 1 (Ehrhart, Stanley).** The function $H_n(t)$ is a polynomial in $t$
> of degree $(n-1)^2$ that satisfies the identities
> $$H_n(-n-t) = (-1)^{n-1}H_n(t),\qquad H_n(-1)=H_n(-2)=\cdots=H_n(-n+1)=0 .$$

Here $H_n(t)$ is the number of $n\times n$ arrays of nonnegative integers whose
rows and columns all sum to $t$ (`MagicSquares.semiMagicCount n t`).

Why this one:

* It is **general $n$** — the direction the user asked for — and it is the
  structural theorem the whole magic-square literature rests on.
* It has a **published elementary proof**: Spencer, *Counting magic squares*,
  Amer. Math. Monthly **87** (1980) 397–399 (reference [14] of BCCG). So the hard
  rung is not research-grade, unlike Ehrhart's general theorem.
* The ladder down to it is **concrete and already partly built**: the $n=2$ rung
  is proved on the platform, the $n=4$ rung is an explicit degree-9 polynomial we
  have already fitted and verified numerically, and $n=3$ is MacMahon's 1915
  formula (also just verified here).
* Mathlib has **no** Ehrhart theory (verified by grep 2026-09-18), so this mission
  genuinely builds new machinery rather than gluing existing lemmas.

Suggested framing: `mission_type: ResearchPaper`, field `combinatorics`,
name **"Magic Squares V: The counting function of semi-magic squares of every order"**.

## 2. Source inventory

| What | Where | Have it? |
|---|---|---|
| BCCG 2003, statements of Theorems 1–5, $n=2,3$ formulas | `referpaper/Beck-Cohen-Cuomo-Gribelyuk - ... (2003).pdf`; text dump `tmp/bccg.txt` | **yes** |
| Spencer 1980, elementary proof of Theorem 1 | Amer. Math. Monthly 87, 397–399 | no — must fetch |
| Anand–Dumir–Gupta 1966 (conjecture), Duke Math. J. 33, 757–769 | reference [2] | no |
| Stanley 1973, *Linear homogeneous Diophantine equations and magic labelings of graphs*, Duke Math. J. 40, 607–632 | reference [15] | no |
| Beck–Pixton, *The Ehrhart polynomial of the Birkhoff polytope*, arXiv:math.CO/0202267 | reference [4] | no — needed for the $n=4$ cross-check |
| MacMahon 1915, $H_3(t)=3\binom{t+3}{4}+\binom{t+2}{2}$ | quoted verbatim in BCCG | **yes** |

Verbatim BCCG quotes already extracted (so the statements can be transcribed
without re-reading the paper):

```
H2(t) = t + 1 , M2(t) = S2(t) = P2(t) = 1 if t even, 0 if t odd
H3(t) = 3 C(t+3,4) + C(t+2,2),  M3(t) = 2/9 t^2 + 2/3 t + 1 if 3|t, 0 otherwise
Theorem 2: Mn, Sn, Pn are quasi-polynomials of degrees n^2-2n-1, n^2/2 - n/2 - 2,
           n^2 - 3n + 2
Theorem 3: H^d_n(t) is a quasi-polynomial of degree (n-1)d
Theorem 4 (Ehrhart), Theorem 5 (Ehrhart-Macdonald reciprocity law)
```

## 3. The ladder (proposed milestones, in attack order)

| # | Milestone | Statement | Source | Status here |
|---|---|---|---|---|
| M1 | $n=1$ | `semiMagicCount 1 t = 1` | trivial | trivial |
| M2 | $n=2$ | `semiMagicCount 2 t = t + 1` | BCCG §1 | **already Proved on the platform** (`86515ed9`) |
| M3 | $n=3$ | `semiMagicCount 3 t = 3 * (t+3).choose 4 + (t+2).choose 2` | MacMahon 1915 | verified numerically, t = 0..10: 1, 6, 21, 55, 120, 231, 406, 666, 1035, 1540, 2211 |
| M4 | $n=4$ | the explicit degree-9 polynomial | Ehrhart polynomial of $B_4$; Beck–Pixton | polynomial fitted and verified on t = 0..14 (coefficients in §4) |
| M5 | degree | a polynomial in $t$ of degree $(n-1)^2$ exists for every $n$ | Spencer 1980 | **the hard rung** |
| M6 | reciprocity | $H_n(-n-t) = (-1)^{n-1}H_n(t)$ | Stanley 1973 / Ehrhart–Macdonald | needs the polynomial from M5 |
| M7 | vanishing | $H_n(-1) = \cdots = H_n(-n+1) = 0$ | same | needs M5 |
| M8 | later | BCCG Theorem 2: $M_n$ is a quasi-polynomial of degree $n^2-2n-1$ | BCCG §2–3 | degree verified for $n=3$ (degree 2) and consistent with $n=4$ (degree 7) |

M1–M4 are each an independent, self-contained target — good "steady output" while
M5 is being attacked. Note M5 does **not** need M3/M4 to be finished.

### Goal statement shape — SETTLED 2026-09-19

Prototype: `examples/magic-squares/mission_v_goal_shape.lean` (`lake env lean`,
compiles; the four shape theorems are `sorry`-ed on purpose, all non-vacuity
`example`s are proved).

```lean
theorem semi_magic_polynomial (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        (∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) ∧
          (∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ))
            = (-1 : ℚ) ^ (n - 1) * p.eval ((t : ℤ) : ℚ)) ∧
            (∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval ((k : ℚ)) = 0)
```

Decisions taken, and why:

1. `∃ p : Polynomial ℚ, …` against `semiMagicCount n t` elaborates without
   trouble — the platform definition `semiMagicCount n t = (semiMagicSquares n t).card`
   is fine as-is, no redefinition needed.
2. 🔴 **`Polynomial.eval₂` does not work for the reciprocity.** It wants a ring
   hom `R →+* S` with `p : R[X]`, and there is no ring hom `ℚ →+* ℤ`; writing
   `p.eval₂ (Int.castRingHom ℚ) (-(n:ℤ) - t)` fails with a type mismatch (it
   insists `p : Polynomial ℤ`). The working encodings are
   **(a)** cast the integer argument into `ℚ` first and use `Polynomial.eval`
   (chosen — reads exactly like BCCG's display),
   **(b)** the polynomial identity `p.comp (C (-(n:ℚ)) - X) = C ((-1:ℚ)^(n-1)) * p`
   (also verified to elaborate; kept as `shape 2b` in the prototype).
3. The vanishing list runs over `1 ≤ k ≤ n - 1` and the condition is `p(-k) = 0`.
   Note the list is **non-empty already at `n = 2`** (`k = 1`), and `H_2`'s
   polynomial `X + 1` does vanish at `-1` — checked in the prototype, together
   with `H_3(-1) = H_3(-2) = 0` on MacMahon's polynomial.
4. `p.natDegree = (n-1)^2` is the right encoding; the `n = 1` corner (degree 0)
   is handled by `Polynomial.natDegree_X_add_C`-style reasoning.

## 4. The $n=4$ rung (M4)

Fitted to $H_4(t)$ for $t=0..14$ and verified to reproduce all 15 values
(10th finite difference identically zero):

$$H_4(t)=\frac{11}{11340}t^{9}+\frac{11}{630}t^{8}+\frac{19}{135}t^{7}+\frac{2}{3}t^{6}
+\frac{1109}{540}t^{5}+\frac{43}{10}t^{4}+\frac{35117}{5670}t^{3}+\frac{379}{63}t^{2}
+\frac{65}{18}t+1$$

Leading coefficient $11/11340$ should equal $\mathrm{vol}(B_4)$; the normalized
volume would then be $9!\cdot 11/11340 = 352$. **Cross-check against Beck–Pixton
before publishing this item** — the coefficient came out of a finite fit, not
from the literature.

Verification data lives in `tmp/order4_counts.py`, `tmp/order4_structure.py`.

## 5. Risk and fallbacks

| Risk | Likelihood | Mitigation |
|---|---|---|
| Spencer's elementary proof needs machinery we must build first (lattice-point counting in cones, or an induction on $n$) | high | treat M1–M4 as the mission's real content; M5 as the stretch goal. Fetch Spencer first and decide. |
| The `∃ p : Polynomial ℚ` goal with reciprocity is awkward in Lean | medium | prototype the statement in `examples/magic-squares/` before drafting the proposal |
| Beck–Pixton disagrees with the fitted $11/11340$ | low (fit verified on 15 points) | it cannot disagree about $H_4$; it could disagree about my reading of "normalized volume" — check the paper |
| Nobody else can contribute because the goal is too hard | medium | the ladder is deliberately front-loaded with independent, easy rungs |

## 6. Alternative line B — order four, special classes (data verified 2026-09-19)

If the general-$n$ rung turns out to be too far, this is a fully verified
order-4 alternative with the same "long path" shape. All numbers below were
computed by `tmp/scout_order4.py` and each polynomial was **re-verified on every
computed point**, not just fitted.

**B1. Symmetric semi-magic squares of order 4** (`IsSemiMagic` + `Mᵀ = M`).
Period-2 quasi-polynomial of degree 6 (the 6 free entries):

| $t$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| count | 1 | 10 | 56 | 214 | 641 | 1620 | 3616 | 7340 | 13825 |

* even $t = 2s$: $1+\frac{16}{3}s+\frac{116}{9}s^2+\frac{52}{3}s^3+\frac{119}{9}s^4+\frac{16}{3}s^5+\frac{8}{9}s^6$
* odd $t = 2s+1$: $10+\frac{119}{3}s+\frac{596}{9}s^2+\frac{178}{3}s^3+\frac{269}{9}s^4+8s^5+\frac{8}{9}s^6$

(leading coefficient $8/9$ on both branches — consistent with a genuine
quasi-polynomial of period 2)

**B2. Symmetric squares of order 4 with the main diagonal also summing to $t$.**
Zero for odd $t$; even part is a degree-5 polynomial in $s=t/2$:

$$1+\frac{47}{12}s+\frac{55}{8}s^{2}+\frac{155}{24}s^{3}+\frac{25}{8}s^{4}+\frac{5}{8}s^{5}$$

**B3. Symmetric magic squares of order 4** (both diagonals).
Zero for odd $t$; the even part is **not** a polynomial in $s$ — it is a
quasi-polynomial of **period 4 in $t$**, degree 4:

| $t$ | 0 | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| count | 1 | 8 | 37 | 112 | 269 | 552 | 1017 | 1728 | 2761 | 4200 | 6141 |

This is exactly BCCG's Theorem 2 in the case $n=4$: degree $n^2/2-n/2-2 = 4$,
and the period divides the lcm of the denominators of the vertices of the
polytope (here 2 in $s$, i.e. 4 in $t$). Splitting by $t \bmod 4$:
$t=4k$ gives $1, 37, 269, 1017, 2761, 6141$ with fourth differences constant
$160$; more terms are needed to pin the $t \equiv 2 \pmod 4$ branch.

**B4. $M_4$ degree is now known from the literature, not guessed.** BCCG
Theorem 2 gives degree $n^2-2n-1 = 7$ for $n=4$, which matches what the
2026-09-18 data could only suggest. Only the **period** is open, and BCCG §4
says how to find it (denominators of the vertices). Our $M_4$ values for
$t=0..12$ are in `missions/project-review-2026-09-18.md` §4.

## 7. Status — the main line was chosen and the proposal is built

The user chose the main line on 2026-09-19. **The proposal exists and is complete:
`3a8476fd-e093-414d-a8d8-e020d2466a57`, status `Draft`.** See `status.md` in this
directory for the full record: 13 items (7 references, 6 drafts), a blind read-back
on every draft, 7 milestones, `main_item_id` = the goal, and a 1528-word description
in the seven-section format.

What remains is the human-only step: review the items and click **Submit Proposal**.
Submitting also grants mission membership to the four definition modules that were
still orphan (`MagicSquaresPandiagonal`, `MagicSquaresMostPerfect`,
`MagicSquaresTransforms`, `MagicSquaresNormal3`), which closes the orphan list.

The order-four alternative in section 6 was **not** taken for this mission; its
numbers remain verified and are recorded in `memory/MAGIC-SQUARES-REF.md` §5 if it is
ever wanted as a separate mission.
