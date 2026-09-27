# Proof: completeness of the four-parameter parametrisation

For all integers $a,b,c,d$ with $a^2+b^2=c^2+d^2$ there are $p,q,r,s$ with
$$a=pr+qs,\quad b=ps-qr,\quad c=pr-qs,\quad d=ps+qr,$$
or the same holds after swapping $c$ and $d$. This is the goal of the mission.

**The argument has three steps, proved inline** (a submission is a single self-contained
file, so the supporting lemmas cannot be imported from the platform graph).

1. **Parity alignment.** A square is $0$ or $1$ modulo $4$ according to the parity of its
   root, so the equation forces the number of odd entries on the two sides to agree. A
   sixteen-way case split on the parities of $a,b,c,d$ leaves six patterns that satisfy this
   counting identity — in each of them $(a-c)$ and $(b-d)$ are both even, or $(a-d)$ and
   $(b-c)$ are — and ten patterns that contradict it. The contradiction is always the same:
   subtracting the four residues shows that $4$ divides a nonzero integer of absolute value
   at most $2$.

2. **The half-sum substitution.** Given $a-c=2k$ and $b-d=2l$, put
   $$X=a-k,\quad Y=k,\quad U=b-l,\quad V=-l .$$
   These are $(a\pm c)/2$ and $(b\pm d)/2$ written without integer division, and they satisfy
   $X+Y=a$, $X-Y=c$, $U-V=b$, $U+V=d$. Substituting $c=a-2k$, $d=b-2l$ into the equation
   gives $k(a-k)+l(b-l)=0$, i.e. $XY=UV$ — the whole content of $a^2+b^2=c^2+d^2$ in the new
   variables.

3. **Factorisation of $XY=UV$.** With $g=\gcd(X,U)$ (degenerate cases $X=0$ or $U=0$ handled
   separately), write $X=rg$, $U=sg$ with $\gcd(r,s)=1$; cancelling $g$ gives $rY=sV$, and
   Bézout for the coprime pair yields $Y=qs$ and $V=qr$ with the *same* $q$. Then
   $a=X+Y=pr+qs$, $b=U-V=ps-qr$, $c=X-Y=pr-qs$, $d=U+V=ps+qr$ with $p=g$.

   The second branch of the parity disjunction is the same computation with $(c,d)$ exchanged:
   the substitution is applied to $(a,b,d,c)$ and produces the swapped parametrisation.

**Why the disjunction is necessary.** Parity alignment only guarantees a matching *after a
possible swap*, and the swap genuinely occurs — for instance $(a,b,c,d)=(1,8,4,7)$ has
$1^2+8^2=4^2+7^2=65$ with $a-c$ odd and $a-d$ even. So no single branch can cover all
solutions, and the statement is deliberately the disjunction rather than one of its halves.

**Scope.** No coprimality, positivity or distinctness is assumed or concluded: every integer
solution, including degenerate ones such as $a=b=c=d=0$ and trivial ones with $(c,d)=\pm(a,b)$,
is covered. The parametrisation is complete but not unique.
