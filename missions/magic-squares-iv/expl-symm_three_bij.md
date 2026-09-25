## The corner parameter enumerates the symmetric order-three magic squares

Let $S_{n}(t)$ be the number of symmetric magic squares of order $n$ and line sum
$t$, and let

$$\mathrm{symmParamSet}(e)=\{0,1,\dots,2e\},\qquad
\mathrm{symmParamCount}(e)=2e+1 .$$

The theorem is

$$S_{3}(3e)=\mathrm{symmParamCount}(e),$$

i.e. the map sending a symmetric magic square of order three and line sum $3e$ to
its top-left corner $M_{00}$ is a bijection onto $\{0,\dots,2e\}$.

### 1. The map lands in the interval

By `symmetric_magic_three_classify`, such a square is
$\mathrm{symmMagic3}(e,a)$ with $a=M_{00}$; its $(0,1)$ entry is the truncated
value $2e-a$. Row $0$ of the square is magic, so

$$a+(2e-a)+e=3e .$$

If $a>2e$ the truncated entry $2e-a$ is $0$ and the left-hand side is $a+e>3e$,
a contradiction. Hence $a\le 2e$ (equivalently $a<2e+1$), so $a$ lies in
$\mathrm{symmParamSet}(e)$.

### 2. Injectivity

By the classification, a square of the filtered family is $\mathrm{symmMagic3}\ e\ a$
with $a$ its own top-left corner. Two members with equal $M_{00}$ are therefore
equal entrywise. Here the elements are arrays over the ambient type
`Square 3 (Fin (3*e+1))`, so the equalities are of *natural numbers*: the proof
compares the coerced entries and transports the classification statement, which
is stated over `Square 3 ℕ`.

### 3. Surjectivity

Given $a\le 2e$, the array $\mathrm{symmMagic3}\ e\ a$ satisfies everything
needed:

* **It is symmetric** — it equals its transpose for every $a$, by inspection.
* **It is magic of line sum $3e$** — each row and column reads
  $a+(2e-a)+e=3e$, the main diagonal $a+e+(2e-a)=3e$ and the anti-diagonal
  $e+e+e=3e$, using $a\le 2e$ for the truncation.
* **All entries are at most $2e$**, since they are among $a$, $2e-a$ and $e$; as
  $2e\le 3e$ the array can be read over `Fin (3*e+1)`, and it is a genuine
  element of the filtered finset.
* Its top-left entry is $a$ again, so it is a preimage of $a$.

### 4. Conclusion

The map is well defined, injective and surjective, so the two finite sets have
the same cardinality: $S_{3}(3e)=\mathrm{symmParamCount}(e)$. Composing with the
cardinality of an interval gives the closed form $S_{3}(3e)=2e+1$, and with
`pan_three_card` and the "otherwise" reductions it yields the full count
$S_{3}(t)=2(t/3)+1$ for $3\mid t$ and $S_{3}(t)=0$ otherwise.

### 5. Formalization notes

* The bijection is set up with `Finset.card_bij` between the filtered finset of
  arrays over `Square 3 (Fin (3*e+1))` and `Finset.range (2*e+1)`, with the map
  `fun M _ => (M 0 0 : ℕ)`. The `change` tactic is used first to expose the two
  concrete finsets, since `symmetricMagicCount` and `symmParamCount` are
  definitionally these cardinalities.
* The only place where truncated subtraction matters is the well-definedness
  step: `a + (2e - a) + e = 3e` has nonnegative solutions exactly for $a\le 2e$,
  and `omega` finds this by splitting on the truncation.
* In the surjectivity step the candidate lift
  `fun i j => ⟨symmMagic3 e a i j, _⟩` needs the entry bound `≤ 3e` for each of
  the nine cells; `fin_cases` plus `simp [symmMagic3]` plus `omega` discharges the
  nine ground instances.
* The auxiliary lemmas for the classification and for the two shape facts
  (`symmMagic3_magic`, `symmMagic3_symmetric`) are kept in a local namespace
  `MagicSquaresSpecial3Aux` of the submission file; they are not separate
  platform nodes.
