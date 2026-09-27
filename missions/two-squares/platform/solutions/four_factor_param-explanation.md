# Proof: parametrizing $XY=UV$ over the integers

Every integer solution of $XY=UV$ admits $p,q,r,s$ with $X=pr$, $Y=qs$, $U=ps$, $V=qr$.

**Degenerate cases first.** If $X=U=0$ take $(p,q,r,s)=(0,1,V,Y)$. If $X=0\ne U$ then
$UV=XY=0$ forces $V=0$ and $(U,Y,0,1)$ works. If $U=0\ne X$ then $Y=0$ and $(X,V,1,0)$ works.
These three cases are disposed of up front, which is what makes the main branch clean.

**Main branch: $X\ne0$ and $U\ne0$.** Let $g=\gcd(X,U)>0$ and, using
`Int.exists_gcd_one`, write $X=rg$ and $U=sg$ with $\gcd(r,s)=1$. Both $r$ and $s$ are
nonzero (otherwise $X$ or $U$ would vanish). Cancelling the nonzero factor $g$ in
$XgY=UgV$ gives
$$rY=sV .$$
From this, $s\mid rY$ and $r\mid sV$. Bézout for the coprime pair gives integers $A,B$ with
$1=rA+sB$, hence
$$Y=Y\cdot1=(rY)A+s(YB),\qquad V=V\cdot1=r(VA)+(sV)B,$$
and every summand on the right is divisible by $s$ (resp. $r$). So $Y=qs$ and $V=q'r$ for
some $q,q'$. Substituting back into $rY=sV$ gives $rsq=rsq'$, and since $rs\ne0$ we may
cancel to get $q=q'$. Taking $p=g$ and this common $q$ gives all four required identities.

**Why Bézout instead of Euclid's lemma.** The library's Euclid lemma for `Int` is stated
with `gcd a c = 1`, so the step $s\mid rY\Rightarrow s\mid Y$ needs $\gcd(s,r)=1$ while
`exists_gcd_one` supplies $\gcd(r,s)=1$; no commutation lemma for `Int.gcd` is available in
this Mathlib pin. Deriving the divisibility from Bézout uses only the supplied orientation
and keeps the proof self-contained.

**Scope.** No coprimality, positivity, or nontriviality is assumed; the statement is exactly
the factorization lemma needed to turn the half-sum substitution back into the four-parameter
parametrisation, and it loses nothing (the identity $pr\cdot qs=ps\cdot qr$ is automatic).
