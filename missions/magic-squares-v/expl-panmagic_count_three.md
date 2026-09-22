## The two-direction panmagic squares of order three

This statement is about `IsPanMagic`, the *strong* predicate: semi-magic, and **both** families of
broken diagonals — descending and ascending — sum to the line sum. That is four extra conditions
on top of magicness (the two offset-$1$ and two offset-$2$ diagonals; the offsets $0$ are already
the two main diagonals).

The ascending conditions kill the cyclic freedom found in the one-direction case. Writing the
array as `a,b,c;d,m,f;g,h,i`, panmagicity in both directions is the conjunction of the eight
magic line sums (three rows, three columns, two main diagonals) with the four extra broken
diagonals `b+f+g = t`, `c+d+h = t`, `a+f+h = t`, `b+d+i = t`. That is twelve linear equations,
and their only nonnegative solution is `a = b = ... = i = e`. The one-direction condition used by
the counting literature asks for only three of those nine diagonal equations (the offsets
`0,1,2` of the descending family), which is why it leaves a two-dimensional family of solutions
rather than a single point.

So the count is $1$ exactly when $3\mid t$ and $0$ otherwise — this submission is a two-line
reduction to the two Mission IV children `pan_three_card` and `pan_three_otherwise`.

**Purpose of this node.** It exists to sit beside `pandiagonal_count_three` so that both readings
of "pandiagonal" are present on the platform. The one-direction reading (Beck--Cohen--Cuomo--
Gribelyuk) gives a degree-two polynomial that never vanishes; the two-direction reading collapses
to the constant square and vanishes off multiples of three. Quoting one in place of the other is
the most likely faithfulness error in this area, and the pair of nodes makes it visible.

### Formalization notes

* The file imports `Theorems.Thm_MagicSquares_pan_three_card` and
  `Theorems.Thm_MagicSquares_pan_three_otherwise` and splits on `3 ∣ t`; in the divisible branch
  it substitutes `t = 3 * e` and applies the first, in the other branch the second.
* Both children are `Proved` platform nodes, so this is a complete proof rather than a sketch.
