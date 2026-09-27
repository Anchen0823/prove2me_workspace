# Proof: the Brahmagupta–Fibonacci identity, both forms

Both statements are polynomial identities in the four variables, so each is discharged by
`ring`: expanding $(p^2+q^2)(r^2+s^2)$ gives
$p^2r^2+p^2s^2+q^2r^2+q^2s^2$, and expanding either right-hand side gives the same four
terms — $(pr\pm qs)^2+(ps\mp qr)^2 = p^2r^2+q^2s^2\pm2pqrs + p^2s^2+q^2r^2\mp2pqrs$.

**Why state it twice.** The two signs are genuinely different representations of the same
product as a sum of two squares, and the four-parameter identity of this mission is exactly
the statement that the two representations are equal. Nothing is assumed about the ring
beyond commutativity, so the lemma is reusable over `ℤ`, `ℚ`, `ZMod n`, and polynomial
rings alike.

**Implementation notes.** A single `constructor <;> ring` closes both conjuncts. No
positivity, ordering, or integrality is used; in particular the identity holds in
characteristic two as well, where the two forms coincide.
