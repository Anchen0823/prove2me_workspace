# Reduction: the goal from the one-form route

This submission reduces the mission's goal,
$\zeta(9)\notin\mathbb Q$, to **two** children.

1. `ZetaNine.irrational_of_small_nonzero_integer_forms` (**Proved**): if a real $x$
   admits nonzero integer forms $b+ax$ of arbitrarily small absolute value, then $x$
   is irrational.
2. `ZetaNine.exponentially_small_nonzero_forms_of_zeta_nine` (**Open**): there is a
   fixed $c>0$ such that, for all sufficiently large $n$, some nonzero integer form
   $b+a\,\zeta(9)$ satisfies $|b+a\,\zeta(9)|<e^{-cn}$.

**Assembly.** Given $\varepsilon>0$, the open child supplies a scale $n$ at which
$e^{-cn}<\varepsilon$ together with a nonzero form of absolute value below $e^{-cn}$;
that form is then below $\varepsilon$, so the criterion applies and yields
irrationality of $\zeta(9)$. Passing from the eventual statement to a single scale
uses $e^{-cn}=(e^{-c})^n$ with $e^{-c}<1$ and the convergence of a geometric
sequence with ratio in $(0,1)$ to $0$.

**Scope and honesty of this reduction.** The child is a strictly **stronger**
statement than the goal, not an equivalent restatement: it demands approximations of
a fixed exponential quality, which a general irrational number need not admit, and
it carries the nonvanishing condition that the zero form would otherwise satisfy
trivially for rational values. The proof content of this reduction is the
quantitative passage from an asymptotic scale to an arbitrary $\varepsilon$; the
mathematical work of the route lives entirely in the open child, which is the
formalisation-free packaging of the local notes' combination of the open lattice
margin J, the Gauss bound, the uniform analytic decay, and the one-sign
nonvanishing certificate. This is the one-form alternative route recorded in the
mission description as $R\leftarrow T,\mathrm{TP},X,A,F$ and
$R\leftarrow T5,\mathrm{FQ},X,A,F$.
