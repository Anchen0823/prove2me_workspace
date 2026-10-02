For a finite bin-packing instance whose item sizes lie strictly between zero and one, we prove

$$LIN(I) \le OPT(I).$$

The argument converts an integral packing into a feasible configuration LP solution. This is the second inequality of Karmarkar–Karp, Lemma 2 (FOCS 1982, p. 313).

Let $P$ be any packing of $I$, and delete its empty bins to obtain $Q$. Deleting empty bins preserves the multiset of packed items and does not increase the number of bins. For every configuration $c$, assign the nonnegative weight

$$x_c=\#\{\text{bins of }Q\text{ equal to }c\}.$$

Only finitely many weights are nonzero. Every such configuration is nonempty, contains only item sizes occurring in $I$, and has total size at most one. For each item size $s$, counting its occurrences across the bins gives

$$\sum_c x_c\,\operatorname{count}_c(s)=\operatorname{count}_I(s).$$

Thus $x$ satisfies every covering constraint of the configuration LP. Its cost is

$$\sum_c x_c=|Q|\le |P|.$$

The set of LP costs is bounded below by zero, so its infimum is at most this feasible cost. Finally, an instance admits a singleton-bin packing. Hence its set of integral packing costs is nonempty, and its least natural-number cost is attained. Applying the construction to a packing with this least cost proves the claim, including the empty instance.

The proof uses only the instance and configuration LP definitions and Mathlib; it assumes no other platform theorem.
