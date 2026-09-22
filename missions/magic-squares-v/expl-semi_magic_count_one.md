## The order-one count: `H_1(t) = 1`

A `1 × 1` semi-magic square of line sum `t` is a single entry whose row sum is that
entry, so the row equation reads `M 0 0 = t`; since the entries live in
`Fin (t + 1)`, that equation has exactly one solution. The filtered finset is
therefore the singleton consisting of the all-`t` array, and its cardinality is `1`.

This is the `n = 1` rung of the ladder towards `semi_magic_polynomial`. The degree
asserted there is `(n-1)^2 = 0`, which a constant polynomial matches, so the base
case is consistent with the general statement rather than a degenerate afterthought.

### Formalization notes

* The statement is proved through `Finset.card_eq_one` followed by
  `Finset.eq_singleton_iff_unique_mem`, which reduces the count to
  *membership of a witness* plus *uniqueness*.
* The witness has to be a **named** term (`let M0 : Square 1 (Fin (t+1)) := …`).
  Writing the array inline as `{fun _ _ => ⟨t, …⟩}` makes the notation elaborate as a
  comprehension rather than a singleton, after which `Finset.eq_singleton_iff_unique_mem`
  no longer matches the goal: Lean reports `Finset.mem_filter` as an unused `simp`
  argument and `constructor` then fails with "target is not an inductive datatype",
  because the membership in question has become a set-membership rather than a
  `Finset` membership. Naming the witness removes the ambiguity.
* Uniqueness is a single `Fin.ext` once the sum is collapsed: the single row sum is
  `∑ j : Fin 1, ↑(M 0 j)`, which `Fin.sum_univ_one` evaluates to the entry `↑(M 0 0)`.
* No `sorry`, no `axiom`; the file is 48 lines.
