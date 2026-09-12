# Boundary-state pushforward for the substituted graph

Let the six embedded gadget edge sets be pairwise disjoint, and let their common boundary-state law be the function $P$ specified by the five hypotheses. For each pair of original vertices and either target level, we prove

$$
\Pr_{\mathrm{sub}}[(x,0)\leftrightarrow(y,l)]
=\Pr_{\mathrm{WZ},P}[(x,0)\leftrightarrow(y,l)].
$$

The argument is a finite pushforward of the product measure. An edge configuration in one gadget determines exactly one of the five partitions of its three attachment vertices. Transitivity and symmetry of graph reachability show that the classifier records all three pairwise connection relations. Injective relabelling preserves the classifier and the configuration weights, so each embedded copy has state mass $P(s)$.

For finite configuration sets $D_i$, classifiers $q_i$, weights $\mu_i$, and state masses

$$
P_i(b)=\sum_{a\in D_i,\ q_i(a)=b}\mu_i(a),
$$

grouping a product sum by the fibres of the coordinatewise classifier gives

$$
\sum_{a\in\prod_iD_i}F(q(a))\prod_i\mu_i(a_i)
=\sum_b F(b)\prod_iP_i(b_i).
$$

This identity uses only finite distributivity; it does not enumerate the configurations or require additional positivity hypotheses.

The proved disjoint-union factorization expresses the substituted-graph probability as a sum over the independent gadget configurations on both levels. The proved boundary-reduction theorem identifies its reachability indicator with the WZ indicator induced by those configurations. Applying the finite pushforward identity to each level gives two sums over state functions. The equivalence between a pair of state functions and a state function on the product of the copy index set with the two levels combines those sums and their product weights into the definition of the WZ probability.

This formalizes the substitution step in Gladkov, Pak, and Zimin, *The bunkbed conjecture is false*, Section 4.2, pp. 6–7. The proof is symbolic and uses no native evaluation.
