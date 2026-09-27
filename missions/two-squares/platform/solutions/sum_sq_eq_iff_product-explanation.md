# Proof: rearrangement into a product equation

For all integers $a,b,c,d$,
$$a^2+b^2=c^2+d^2\iff (a+c)(a-c)=(d+b)(d-b).$$

**Argument.** Both directions are the same computation read backwards. The two products expand
to $a^2-c^2$ and $d^2-b^2$ respectively, so the right-hand equation says
$a^2-c^2=d^2-b^2$, i.e. $a^2+b^2=c^2+d^2$ after moving $b^2$ and $c^2$ across. Both directions
are therefore linear consequences of the two polynomial identities
$(a+c)(a-c)=a^2-c^2$ and $(d+b)(d-b)=d^2-b^2$, each supplied to `nlinarith` as a `by ring`
fact.

**Why this form.** Writing the right-hand side as $(d+b)(d-b)$ rather than $(b+d)(d-b)$ keeps
both factors in the order in which the half-sum substitution later needs them: with
$X=(a+c)/2$, $Y=(a-c)/2$, $U=(b+d)/2$, $V=(d-b)/2$ the equation becomes $XY=UV$ with no extra
sign juggling.

**Scope.** The statement is an equivalence with no hypotheses, so it loses no information and
imposes nothing on $a,b,c,d$; signs and zeros are all allowed.
