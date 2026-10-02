For the rounded part $J$ of geometric grouping applied to any multiset $I$ of real numbers, there is a multiset of pairs satisfying

$$\pi_1(M)=J,\qquad \pi_2(M)\le I,\qquad a\le b\quad((a,b)\in M).$$

The construction assigns each rounded item to a distinct occurrence in the preceding group. It uses only the sorted order, so it is valid for every natural grouping parameter and does not require positivity of the input.

Let $A,G$ be consecutive groups. Pair the head of $G$ with every item in the prefix of $A$ of length $|G|$. The number of such pairs is

$$\min(|A|,|G|),$$

which is exactly the number of rounded items contributed by $G$: the definition takes the first $|A|$ items of $G$ and rounds all of them to its head. Therefore the first projection of these pairs agrees, including multiplicities, with the rounded contribution of $G$.

Each original group supplies source occurrences only once, as the predecessor of the next group. The second projections are prefixes of these source groups, hence their multiset sum is bounded by the multiset sum of all groups. The greedy prefix and remaining suffix concatenate to the input list at each recursive cut; consequently the groups partition the sorted input and their multiset sum is $I$.

Finally, flattening the groups preserves the sorted input list. Every item of a preceding group is at least every item of the following group, in particular its head. This proves the componentwise inequality for every constructed pair. An empty following group contributes no pairs, and an empty list of groups gives the empty certificate.
