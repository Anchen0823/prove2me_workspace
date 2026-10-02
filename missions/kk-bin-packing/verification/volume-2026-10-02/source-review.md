# Lemma 2 contribution: source and boundary review

The live target is `5455998b-e4e9-4edb-92fc-4effa3b071a2`, the captain-attested
Lemma 2 milestone in mission `359adb44-9a24-441c-8a2b-bd71395fcad4`.
The current target, audits, empty submission history, milestone history and
discussion are saved in this directory. No prior rejected formalization was found.

Source: Karmarkar and Karp, *An Efficient Approximation Scheme for the
One-Dimensional Bin-Packing Problem*, FOCS 1982, p. 313, Lemmas 1 and 2.
https://pagesperso.g-scop.grenoble-inp.fr/~newmana/OptApproxFall2016/Karmarker-Karp-BinPacking.pdf

The source separates the volume lower bound, the LP lower bound on the integer
optimum, and the rounding upper bound. The volume proof weights each demand
constraint by its item size; every configuration then contributes at most its
LP weight. The Lean proof also establishes nonemptiness of the feasible-cost set
before taking its infimum. This handles the empty instance without relying on
the default value of an empty infimum.

The platform's existing instance definition uses real sizes strictly between
zero and one. The original introductory model uses rational sizes; the volume
argument and the finite-dimensional LP/rounding statements extend to the real
model already fixed by the captain. No definitions or target hypotheses are changed.

The LP-to-integer lower bound is already published as
`555b051c-6aa5-4769-866f-a595b8c60e2c`. Its prior submission
`956de592-7e80-4f94-ae20-f0b7fe913d4e` was rechecked as ACCEPTED during this work;
it is reused, not counted as a new proof in this contribution.

Independent review: GPT-6 Luna checked the weighted-count argument, empty
instance, infimum nonemptiness, real-size extension and non-circular dependencies.
GPT-6.1 Sol constructs the new direct volume proof; GPT-6 Astra develops the
rounding reduction. Only the primary agent performs platform writes.

The refined upper-bound decomposition uses two explicit open cores: a sparse
near-optimal feasible LP vector, and a general floor-rounding certificate. The
conditional reduction proves existence of optimal integer packings, gluing of
the principal/residual packings, averaging of two residual bounds, and the
positive-tolerance argument for the real LP infimum.

The independent reviewer checked the certificate under overcoverage. In Lean,
multiset subtraction truncates per-type counts; hence the unchanged full floor
configurations define the correct residual even when they contain extra items.
The existential principal packing is of `I - R` and must trim excess slots.
No assumption that the full floor configurations form a submultiset of `I` is
made. For each type the residual count is bounded by the fractional slot supply;
weighting by type size gives the volume bound, and one configuration copy per
fractional support entry gives the residual packing count bound. Both core
statements include empty instances and remain open in this contribution.

Baseline workspace check: the two pre-existing unassigned five-primes solutions
remain outside this task. Baseline mission build passed with its existing four
selected roots; warnings in theorem mirrors are expected platform placeholders.
