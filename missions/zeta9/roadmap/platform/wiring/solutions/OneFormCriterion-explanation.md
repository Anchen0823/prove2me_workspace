# Proof: one-form irrationality criterion

The submission proves, for an arbitrary real $x$,

> if for every $\varepsilon>0$ there is an integer form $b+ax$ that is **nonzero**
> and satisfies $|b+ax|<\varepsilon$, then $x$ is irrational.

**Argument.** Assume $x=p/q$ with $q\neq 0$ and apply the hypothesis with
$\varepsilon=1/|q|$, obtaining $(b,a)$ with $0<|b+a\,p/q|<1/|q|$. Multiplying by
$|q|$ gives $0<|bq+ap|<1$, while $bq+ap$ is an integer; hence $bq+ap=0$, i.e.
$b+a\,p/q=0$, contradicting the nonvanishing hypothesis. Therefore $x\notin\mathbb Q$.

**Formal steps.** `irrational_iff_ne_rational` reduces the goal to excluding
$x=p/q$. The form $b+a\,p/q$ is cleared to the integer $bq+ap$ divided by $q$ inside
the absolute value, the strict inequality is transported across the positive
denominator, and `Int.abs_lt_one_iff` forces $bq+ap=0$.

**Scope.** This is the criterion half of local node TP. It says nothing about the
$\zeta(9)$ construction: it is a reusable statement about an arbitrary real number,
and it is the module imported by the goal's one-form reduction.
