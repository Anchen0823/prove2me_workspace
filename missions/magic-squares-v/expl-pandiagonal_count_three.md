## The order-three pandiagonal count: $P_{3}(t)=\binom{t+2}{2}$

**Structure.** Let $M$ be a $3\times3$ array of nonnegative integers which is semi-magic of line
sum $t$ and whose three wrapped diagonals parallel to the main diagonal also sum to $t$:
$M_{00}+M_{11}+M_{22}=t$, $M_{01}+M_{12}+M_{20}=t$, $M_{02}+M_{10}+M_{21}=t$. Together with the
three rows and the three columns these nine equations are linear, and they force

$$M_{10}=M_{01},\quad M_{11}=M_{02},\quad M_{12}=M_{00},\quad
M_{20}=M_{02},\quad M_{21}=M_{00},\quad M_{22}=M_{01}.$$

In other words $M_{ij}=g(i+j)$ for the single function $g$ on $\mathbb{Z}/3$ given by
$g(0)=M_{00}$, $g(1)=M_{01}$, $g(2)=M_{02}$ — each wrapped diagonal of $M$ is a cyclic rotation of
$(g(0),g(1),g(2))$, which is exactly why all of them have the same sum. Conversely, for any
$g : \mathbb{Z}/3\to\mathbb{N}$ the array $g(i+j)$ is semi-magic with all three wrapped diagonals
equal to $g(0)+g(1)+g(2)$.

**Count.** The line sum is $g(0)+g(1)+g(2)=t$, so the squares correspond bijectively to the
triples of naturals summing to $t$ — equivalently, since $g(0)$ is determined by $g(1),g(2)$, to
the pairs $(a,b)$ with $a+b\le t$. That set has $\sum_{a=0}^{t}(t-a+1)=\binom{t+2}{2}$ elements.

The result is Beck--Cohen--Cuomo--Gribelyuk's $P_{3}$, a degree-two polynomial never vanishing:
$1,3,6,10,15,21,\dots$, inside their theorem that $P_{n}$ is a quasi-polynomial of degree
$n^{2}-3n+2$. It must not be confused with `panMagicCount 3`, which additionally requires the
*ascending* broken diagonals to sum to the line sum; that stronger condition leaves only the
constant square and vanishes off multiples of three.

### Formalization notes

* The bijection is `Finset.card_bij` from the filtered finset to
  `(Finset.range (t+1)).sigma (fun a => Finset.range (t - a + 1))`, with the map
  `fun M _ => ⟨(M 0 1 : ℕ), (M 0 2 : ℕ)⟩`. The structure lemma supplies injectivity (the top row
  is recovered from row $0$), and surjectivity builds the array from `g` defined by
  `if (k : ℕ) = 0 then t - a - b else if (k : ℕ) = 1 then a else b`.
* The cardinality of the pair set is evaluated by `Finset.card_sigma`, the reflection identity
  `Finset.sum_range_reflect` turning $\sum(t-a+1)$ into $\sum(a+1)$, and Pascal's rule
  `Nat.choose_succ_succ'` with `Nat.choose_one_right`.
* Defining `g` by an `if` on the *value* `(k : ℕ)` rather than by vector notation `![…]` keeps
  every subsequent reduction decidable, so `simp` discharges the nine line-sum checks without any
  Fin-index bookkeeping.
