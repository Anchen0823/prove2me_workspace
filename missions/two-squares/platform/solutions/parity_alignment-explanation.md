# Proof: parity alignment after a possible swap

If $a^2+b^2=c^2+d^2$ then $(a-c)$ and $(b-d)$ are both even, or else $(a-d)$ and $(b-c)$ are
both even — i.e. after possibly swapping $c$ and $d$, matching entries have the same parity.

**The real content is modulo 4, not modulo 2.** A square is $0$ mod $4$ when its root is even
and $1$ mod $4$ when its root is odd, so $a^2+b^2=c^2+d^2$ forces
$$\#\{\text{odd entries among }a,b\}=\#\{\text{odd entries among }c,d\}.$$
Modulo $2$ alone only gives that the two counts have the same parity, which is too weak — the
pattern $(a,b)$ even-even against $(c,d)$ odd-odd passes mod $2$ ($0\equiv 0$) but fails mod $4$
($0\not\equiv 2$). This is why the proof cannot be shortened to a mod-2 argument.

**Structure of the proof.** Three small facts are established locally, all from witnesses
rather than from a parity library:

1. even $-$ even is even, and odd $-$ odd is even (subtract the witnesses);
2. an even square is divisible by $4$ ($x=2k\Rightarrow x^2=4k^2$), and an odd square minus $1$
   is divisible by $4$ ($x=2k+1\Rightarrow x^2-1=4k(k+1)$);
3. a "clash" lemma: if each of $a^2,b^2,c^2,d^2$ is reduced modulo $4$ to a residue
   $r\in\{0,1\}$ and $r_a+r_b\ne r_c+r_d$, then the equation is impossible — subtracting the
   residues shows $4\mid(r_c+r_d-r_a-r_b)$, a nonzero integer strictly between $-4$ and $4$.

Then the proof splits on the parity of $a,b,c,d$ (sixteen cases). Six cases satisfy the
counting identity and are closed by (1): the four-all-equal cases and the two-swapped cases
give the left disjunct, and the two cases $(a,b)\equiv(d,c)$ give the right one. The remaining
ten cases contradict the counting identity and are closed by (3) with concrete residues;
`norm_num` discharges the two numeric side conditions in each.

**Scope.** The statement carries no hypotheses beyond the equation itself, and no case is
vacuous: all sixteen parity patterns are genuinely considered, and the disjunction is not
exclusive — for instance $(a,b,c,d)$ all even satisfies both branches.
