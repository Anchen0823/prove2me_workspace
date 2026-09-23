# Matching coefficients as bottom Mobius weights

Platform verification: theorem `2436e4cb-003b-423c-bd3a-318933165075` is now
**Proved**, after submission `a3ef28e8-7f34-45b9-bafe-469d3037038d` was accepted
on 2026-09-23. Exact source hashes and the corrected-entry-point audit are in
`verification/matching-coefficient-mobius-platform-record.json`.

For n >= 1 let P be the inclusion poset of matching-covered boards, with the
empty board adjoined as bottom. Write a(B) for the public matching Euler
coefficient. The relevant identity is

    a(B) = -mu_P(empty, B)    for B nonempty.

The bottom is exceptional: a(empty) = 0, whereas mu_P(empty, empty) = 1.
Accordingly `matchingMobiusWeight` assigns 1 at bottom and -a(B) elsewhere.

The proof uses the already established identity

    sum_{C subset B} a(C) = [B contains a perfect matching].

Terms outside P vanish, so restricting to P preserves this sum. Every nonempty
member of P contains a perfect matching. It follows that the prefix sums of the
corrected weight are 1 at bottom and 0 everywhere else. Finite-order induction
shows that these conditions uniquely determine the bottom Mobius function.

`MatchingMobius.lean` also transfers each coefficient interval sum with a
nonempty lower endpoint to the negative sum of bottom Mobius values over the
same interval in P. This is an unconditional equality, not an assumed Euler
identity. The separate `FiniteMobiusTransport.lean` lemma makes bottom Mobius
values invariant under order isomorphism.

`SemiMagicFaceMobius.lean` now performs the transport to the actual finite
geometric face poset. It constructs the zero-face bottom and locally finite
order instances and proves `matchingCoefficient_face_eq_neg_mu` there.

Combined with the accepted face-support order isomorphism, this removes the
coefficient-identification issue from the mathematical roadmap. It does not
prove Eulerianity: for an arbitrary finite poset, sums of bottom Mobius values
over upper intervals need not vanish. The geometric local Euler theorem remains
the missing input. No new Open platform child should be introduced merely to
restate that input.

Verification: the integrated build completed successfully (8752 jobs), and the
coefficient formula, interval formula, order-isomorphism transport and geometric
face formula all have only the standard axioms. See
`verification/face-mobius-build.log` and `verification/matching-mobius-axioms.log`.
