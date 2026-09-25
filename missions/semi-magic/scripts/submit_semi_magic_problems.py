# -*- coding: utf-8 -*-
"""Submit the four child nodes of the semi-magic mission."""
import io, json, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")
OUT = os.path.join(ROOT, "missions", "semi-magic")

PRE_COMP = "import Mathlib\nimport Definitions.Def_MagicSquaresCompositions\nopen MagicSquares"
PRE_SM3 = ("import Mathlib\nimport Definitions.Def_MagicSquares\n"
           "import Definitions.Def_MagicSquaresSemiMagic3\nopen MagicSquares")
SRC = ("P. A. MacMahon, Combinatory Analysis (1915); M. Beck, T. Cohen, J. Cuomo, P. Gribelyuk, "
       "The number of \"magic\" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), "
       "707-717; arXiv:math/0201013v3, Section 2, Theorem 1.")

P_COMP = {
 "theorem_name": "MagicSquares.comps_card",
 "theorem_title": "Stars and bars: the number of compositions of n into k parts",
 "formal_statement": ("namespace MagicSquares\n\n"
   "theorem comps_card (N k n : ℕ) (hn : n ≤ N) :\n"
   "    (comps N (k + 1) n).card = (n + k).choose n := by sorry\n\n"
   "end MagicSquares"),
 "natural_language_statement": r"""**Stars and bars.** The number of compositions of $n$ into
$k+1$ nonnegative parts is

$$\#\{x\in\mathbb{N}^{k+1} : x_{0}+\cdots+x_{k}=n\}=\binom{n+k}{n}.$$

This is the classical stars-and-bars count, stated in the boxed form used
throughout the mission: `comps N (k+1) n` is the finite set of functions
$\mathrm{Fin}(k+1)\to\mathrm{Fin}(N+1)$ whose values sum to $n$, and the
hypothesis $n\le N$ guarantees the box is inactive — every coordinate of such a
tuple is at most $n$, hence at most $N$.

**Proof.** Splitting off the first coordinate identifies compositions of $n$
into $k+2$ parts with the disjoint union, over $i=0,\dots,n$, of the
compositions of $n-i$ into $k+1$ parts; this gives the recurrence
$c(k+1,n)=\sum_{i\le n}c(k,n-i)$ with $c(0,n)=[n=0]$. The binomial
$\binom{n+k}{n}$ satisfies the same recurrence by the hockey-stick identity
$\sum_{j\le n}\binom{j+k}{j}=\binom{n+k+1}{n}$, which is itself an immediate
induction from Pascal's rule.

**Formalization Note** The count is taken inside a fixed box $\mathrm{Fin}(N+1)$
because $\mathbb{N}^{k}$ has no `Fintype`; holding $N$ fixed while $k$ and $n$
vary is what lets the induction avoid any reindexing of the tail.""",
 "preamble": PRE_COMP, "source": SRC,
 "tags": ["combinatorics", "enumerative-combinatorics"],
}

P_CANON = {
 "theorem_name": "MagicSquares.sm3_canonical",
 "theorem_title": "Canonical decomposition of a 3x3 semi-magic square",
 "formal_statement": ("namespace MagicSquares\n\n"
   "theorem sm3_canonical (M : Square 3 ℕ) (t : ℕ) (hM : IsSemiMagic M t) :\n"
   "    ∃ u v w x y z : ℕ,\n"
   "      M = sm3Of u v w x y z ∧\n"
   "        u + v + w + x + y + z = t ∧\n"
   "          min x (min y z) = 0 ∧\n"
   "            ∀ u' v' w' x' y' z' : ℕ,\n"
   "              M = sm3Of u' v' w' x' y' z' →\n"
   "                min x' (min y' z') = 0 →\n"
   "                  u' = u ∧ v' = v ∧ w' = w ∧ x' = x ∧ y' = y ∧ z' = z := by sorry\n\n"
   "end MagicSquares"),
 "natural_language_statement": r"""Every $3\times3$ semi-magic square with
nonnegative integer entries and line sum $t$ can be written **uniquely** as a
nonnegative integer combination

$$M=u\,D+v\,E+w\,F+x\,A+y\,B+z\,C$$

of the six order-three permutation matrices, normalized by
$\min(x,y,z)=0$. Here $D,E,F$ are the three even transversals (the identity and
the two $3$-cycles) and $A,B,C$ the three odd ones (the transpositions).

**Existence.** Put $u=\min D$, $v=\min E$, $w=\min F$ and subtract
$uD+vE+wF$; the residual $M'$ is again semi-magic and each of its three even
transversals has minimum $0$. Writing $M'$ in the four-parameter form
$$\begin{pmatrix} a & b & t'-a-b\\ c & d & t'-c-d\\
t'-a-c & t'-b-d & a+b+c+d-t'\end{pmatrix},$$
the three vanishing minima read
$$\min(a,d,a+b+c+d-t')=\min(b,t'-c-d,t'-a-c)=\min(t'-a-b,c,t'-b-d)=0.$$
If $b>c$ then each of the three ways for the middle minimum to vanish forces
the opposite inequality: $b=0$ is impossible, $t'-c-d=0$ gives $c+d=t'$ and
hence $b\le c$ from $b+d\le t'$, and $t'-a-c=0$ gives $a+c=t'$ and hence
$b\le c$ from $a+b\le t'$. So $b\le c$, and symmetrically $c\le b$; thus
$b=c$, which is exactly the statement that $M'$ is a combination of $A,B,C$
alone.

**Uniqueness.** The normalization is essential: without it the single relation
$D+E+F=A+B+C$ (both sides equal the all-ones matrix) would identify distinct
$6$-tuples. With $\min(x,y,z)=0$ the coefficients are recovered from $M$ by
$u=\min D$, $v=\min E$, $w=\min F$ and $x=M_{00}-u$, $y=M_{11}-u$, $z=M_{01}-v$.

**Formalization Note** `sm3Of` is defined over $\mathbb{N}$ with truncated
subtraction where necessary, so every recovery identity has to be stated with
the admissibility inequalities as explicit hypotheses.""",
 "preamble": PRE_SM3, "source": SRC,
 "tags": ["combinatorics", "magic-squares", "enumerative-combinatorics"],
}

P_BIJ = {
 "theorem_name": "MagicSquares.sm3_bij",
 "theorem_title": "Bijection between semi-magic squares and normalized parameters",
 "formal_statement": ("namespace MagicSquares\n\n"
   "theorem sm3_bij (t : ℕ) : semiMagicCount 3 t = sm3Count t := by sorry\n\n"
   "end MagicSquares"),
 "natural_language_statement": r"""The map

$$(u,v,w,x,y,z)\longmapsto uD+vE+wF+xA+yB+zC$$

is a bijection from the normalized coefficient vectors — six nonnegative
integers summing to $t$ with $\min(x,y,z)=0$ — onto the $3\times3$ semi-magic
squares of line sum $t$. Consequently

$$H_{3}(t)=\mathrm{sm3Count}(t).$$

Surjectivity and injectivity are exactly the two halves of `sm3_canonical`;
what is left is the bookkeeping that turns a bijection of carriers into an
equality of `Finset.card`s. Two coercions have to be handled explicitly. First,
`semiMagicCount 3 t` counts arrays with entries in `Fin (t+1)`, so the forward
map must be read into that finite type — legitimate because every entry of a
semi-magic square of line sum $t$ is at most $t$. Second, `sm3Count t` counts
functions `Fin 6 → Fin (t+1)`, and the bound is again lossless because the six
coefficients sum to $t$.

**Formalization Note** Both directions therefore need a `Finset.card_bij`
with an explicit proof that the round trip is the identity on each side.""",
 "preamble": PRE_SM3, "source": SRC,
 "tags": ["combinatorics", "magic-squares", "enumerative-combinatorics"],
}

P_CARD = {
 "theorem_name": "MagicSquares.sm3_params_card",
 "theorem_title": "Counting the normalized coefficient vectors",
 "formal_statement": ("namespace MagicSquares\n\n"
   "theorem sm3_params_card (t : ℕ) :\n"
   "    sm3Count t = 3 * ((t + 3).choose 4) + ((t + 2).choose 2) := by sorry\n\n"
   "end MagicSquares"),
 "natural_language_statement": r"""The number of normalized coefficient vectors —
six nonnegative integers summing to $t$ whose odd part $(x,y,z)$ has minimum
$0$ — is

$$\mathrm{sm3Count}(t)=3\binom{t+3}{4}+\binom{t+2}{2}.$$

**Proof.** Partition the vectors according to the *first* zero among
$(x,y,z)$. If $x=0$ the remaining five coordinates are arbitrary nonnegative
integers summing to $t$, giving $\binom{t+4}{4}$ vectors. If $x>0$ and $y=0$,
subtract $1$ from $x$ and the remaining five coordinates sum to $t-1$, giving
$\binom{t+3}{4}$. If $x>0$, $y>0$ and $z=0$, subtract $1$ from each of $x$ and
$y$ and the remaining five sum to $t-2$, giving $\binom{t+2}{4}$. Hence

$$\mathrm{sm3Count}(t)=\binom{t+4}{4}+\binom{t+3}{4}+\binom{t+2}{4}.$$

Two applications of Pascal's identity collapse this to MacMahon's form:
$\binom{t+4}{4}=\binom{t+3}{4}+\binom{t+3}{3}$ and
$\binom{t+3}{4}=\binom{t+2}{4}+\binom{t+2}{3}$, so the sum equals
$3\binom{t+3}{4}+\bigl(\binom{t+3}{3}-\binom{t+2}{3}\bigr)$, and one more
instance of Pascal gives $\binom{t+3}{3}-\binom{t+2}{3}=\binom{t+2}{2}$.

**Formalization Note** The three counts of five-part compositions come from
`comps_card`. Because all arithmetic stays in $\mathbb{N}$, the Pascal steps
must be arranged so that no subtraction is truncated.""",
 "preamble": PRE_SM3, "source": SRC,
 "tags": ["combinatorics", "magic-squares", "enumerative-combinatorics"],
}

def main():
    payload = {"problems": [P_COMP, P_CANON, P_BIJ, P_CARD]}
    path = os.path.join(OUT, "submit-problems-batch1.json")
    with io.open(path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=1)
    r = subprocess.run([PY, API, "post", "/submit-problem", path], cwd=ROOT,
                       capture_output=True, text=True)
    print(r.stdout[:3000])
    print(r.stderr[:800])

if __name__ == "__main__":
    main()
