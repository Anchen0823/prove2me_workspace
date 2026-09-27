# Proof: the four-parameter identity

The claim is that for all integers $p,q,r,s$,
$$(pr+qs)^2+(ps-qr)^2=(pr-qs)^2+(ps+qr)^2 .$$

**Argument.** It is a polynomial identity over `ℤ`, so `ring` proves it directly: after
expansion both sides equal $p^2r^2+p^2s^2+q^2r^2+q^2s^2$; the cross terms $\pm2pqrs$ cancel
within each side. Conceptually the identity says the two Brahmagupta–Fibonacci
representations of the same product $(p^2+q^2)(r^2+s^2)$ coincide, which is why the
quadruple $(pr+qs,\,ps-qr,\,pr-qs,\,ps+qr)$ solves $a^2+b^2=c^2+d^2$ for free.

**Scope.** No hypothesis is needed and none is assumed: the statement is unconditional and
holds for negative and for zero parameters as well. It is stated over `ℤ` because that is
the setting of the mission's parametrisation problem; the same proof works verbatim over any
commutative ring.
