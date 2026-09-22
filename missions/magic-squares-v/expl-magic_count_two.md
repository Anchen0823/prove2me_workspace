## The order-two magic count: $M_{2}(t)$ is $1$ for even $t$ and $0$ otherwise

By the structure of a $2\times2$ semi-magic square, the main diagonal reads $2M_{00}$ and the
anti-diagonal reads $2(t-M_{00})$. A magic square asks for both to equal $t$:

$$2M_{00}=t\quad\text{and}\quad 2(t-M_{00})=t .$$

The first already forces $t$ to be even and $M_{00}=t/2$, and then the second holds
automatically. So for even $t$ there is exactly one square — the constant array with every entry
$t/2$ — and for odd $t$ there is none.

This is the first instance of the divisibility obstruction that recurs at every order: the
diagonal conditions are not implied by semi-magicity, and they vanish off a sublattice of line
sums (at order three the obstruction becomes $3\mid t$, via the centre entry).

### Formalization notes

* Case split on `2 ∣ t`. For the even branch the proof exhibits the constant square `C` with
  entries `e = t/2`, shows it is a member with `Finset.eq_singleton_iff_unique_mem`, and proves
  that any other member equals it entrywise.
* For the odd branch, `Finset.card_eq_zero` plus `Finset.not_nonempty_iff_eq_empty` reduces the
  statement to the absence of a square, and the witness for the contradiction is `M 0 0` itself:
  the two diagonal equations give `t = 2 * (M 0 0 : ℕ)`.
