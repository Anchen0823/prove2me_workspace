## The order-two semi-magic count: $H_{2}(t)=t+1$

A $2\times2$ semi-magic square of line sum $t$ has rows and columns summing to $t$. The first
row and first column give $M_{00}+M_{01}=t$ and $M_{00}+M_{10}=t$, so $M_{01}=M_{10}$; the
second row then gives $M_{11}=M_{00}$. Hence every such square is

$$\begin{pmatrix} a & t-a\\ t-a & a\end{pmatrix},\qquad a=M_{00},$$

and $a$ ranges over $0,\dots,t$ freely. The count is therefore $t+1$.

### Formalization notes

* The bijection is `Finset.card_bij` from the filtered finset of arrays over `Square 2 (Fin (t+1))`
  to `Finset.range (t+1)`, with the map `fun M _ => (M 0 0 : ℕ)`. Well-definedness is just
  `(M 0 0).isLt`; injectivity uses the structure lemma; surjectivity builds
  `![![a, t-a], [t-a, a]]`.
* Injectivity is proved by first deriving the four *numeral-index* equalities
  `(M₁ 0 j : ℕ) = (M₂ 0 j : ℕ)` by `omega`, and then closing the `fin_cases` goals with `exact`.
  Going the other way — proving the equalities *after* `fin_cases` by `omega` — does not work,
  because `fin_cases` leaves the Fin indices as explicit `Fin.mk` terms whose proof components
  differ from the ones in the hypotheses, and `omega` compares atoms syntactically. `simp`/`exact`
  compare up to definitional equality and are unaffected.
