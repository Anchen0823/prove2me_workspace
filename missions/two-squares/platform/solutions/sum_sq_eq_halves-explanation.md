# Proof: existence of the half-sum variables

If $a^2+b^2=c^2+d^2$ and $a-c$ and $b-d$ are even, then there are integers $X,Y,U,V$ with
$$X+Y=a,\quad X-Y=c,\quad U-V=b,\quad U+V=d,\quad XY=UV .$$

**Construction.** Write $a-c=2k$ and $b-d=2l$ (the parity hypotheses give exactly this). Then
take
$$X=a-k,\quad Y=k,\quad U=b-l,\quad V=-l .$$
The four linear conditions are pure arithmetic: $X+Y=a$, $X-Y=a-2k=c$, $U-V=b$, $U+V=b-2l=d$.

**Why these choices.** They are the half-sums $(a+c)/2$, $(a-c)/2$, $(b+d)/2$, $(d-b)/2$ written
without integer division: expressing the parameters through the *witnesses* $k,l$ instead of
through `/2` keeps every step inside polynomial arithmetic and avoids any parity lemma about
division.

**The product equation.** Substituting $c=a-2k$ and $d=b-2l$ into $a^2+b^2=c^2+d^2$ and
expanding gives $-4ak+4k^2-4bl+4l^2=0$, i.e. $k(a-k)+l(b-l)=0$, i.e.
$(a-k)k=(b-l)(-l)$, which is $XY=UV$. `nlinarith` finds this as a rational multiple of the
rewritten hypothesis, so no manual rearrangement is needed.

**Scope.** Only the two stated parity hypotheses are used. Note $a+c$ and $b+d$ need no separate
hypothesis: they differ from $a-c$ and $b-d$ by $2c$ and $2d$ respectively.
