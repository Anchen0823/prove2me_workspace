# Reduction: the goal from the two-form route

This submission reduces the mission's goal,
$\zeta(9)\notin\mathbb Q$, to **two** children.

1. `ZetaNine.irrational_of_two_small_integer_forms` (**Proved**): if a real $x$
   admits two non-proportional integer forms in $1$ and $x$ of arbitrarily small
   absolute value, then $x$ is irrational.
2. `ZetaNine.exponentially_small_independent_forms_of_zeta_nine` (**Open**): there is
   a fixed $c>0$ such that, for all sufficiently large $n$, there are integers
   $b_1a_2\neq b_2a_1$ with both $|b_i+a_i\,\zeta(9)|<e^{-cn}$.

**Assembly.** Given $\varepsilon>0$, choose a scale $n$ with $e^{-cn}<\varepsilon$;
the open child provides two independent forms of absolute value below $e^{-cn}$ at
that scale, hence below $\varepsilon$, and the two-form criterion gives
irrationality of $\zeta(9)$. The passage from the eventual statement to a single
scale again uses $e^{-cn}=(e^{-c})^n$ with ratio $e^{-c}\in(0,1)$.

**Scope and honesty of this reduction.** This is the mission's main line, matching
the reduction $R\leftarrow J,F,A,G,P$ recorded in the mission description: the child
packages the four local ingredients — the open exponential margin J, the coefficient
map F, the analytic decay A and the Gauss lattice bound G — into the single
obligation that two independent small forms exist with a fixed exponential rate. The
child is strictly stronger than the goal (it requires two non-proportional forms
along one sequence of scales) and is not an equivalent restatement of it. The
mathematical work of the route lives entirely in the child; the formal content of
this submission is the quantitative extraction of a single scale from the asymptotic
statement together with the correct independence and smallness bookkeeping.
