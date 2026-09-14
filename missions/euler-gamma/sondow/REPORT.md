# Sondow decomposition of Euler's constant irrationality

Subsequent progress: [analytic continuation report](CONTINUATION-REPORT.md) records three additional ACCEPTED proofs and two SKETCH_ACCEPTED reductions. The original report below records the initial branch submission.

Target: `EulerMascheroni.gamma_irrational`, theorem `66a4e48a-f260-4615-92d3-686ca9356509`.

This contribution adds an independent Sondow route to the target. It does not establish the irrationality of Euler's constant. The exact definitions, English statements, source references and explanations are preserved in this directory's payload files.

Final server result (2026-09-14): the target reduction is **SKETCH_ACCEPTED**, the independent integrality proof is **ACCEPTED**, and the target remains **Open**. The new decomposition was read back from the server and contains exactly the four children below, one Proved and three Open. All four published statements match the locally checked statements.

The reduction has four children:

| Child | Mathematical role | Theorem ID |
|---|---|---|
| `integral_identity` | Known integral evaluation, awaiting formalization | `747d96a7-9576-41e1-801a-228e9d36c4cd` |
| `scaled_integral_bounds` | Known positive remainder estimate, awaiting formalization | `00b4cd42-5f36-4d22-ab0f-2a87c9194496` |
| `scaled_A_integral` | Denominator clearing, server ACCEPTED without open dependencies | `e968787d-5f26-4338-af7e-74888eaf4d79` |
| `fractional_lower_bound_conjecture` | Unresolved infinite-occurrence condition | `ebf8a88e-ef15-4154-8773-6ee4404e2d96` |

The definition `eulerMascheroni_sondow` was published as `b3aa1aab-7502-4c10-9f7b-e005a6771e56`. It uses the logarithmic form directly, so a separate formal proof identifying it with the logarithm of an integer is unnecessary for this reduction.

## Validation

The toolchain is Lean v4.33.1 with Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`, matching the platform target. All checks use `autoImplicit=false`.

- The definition and four child statements compile locally.
- The integrality proof compiles; `#print axioms solution` lists only `propext`, `Classical.choice`, and `Quot.sound`.
- The exact-target sketch compiles using child theorem modules. Its local `sorryAx` comes from imported child placeholders, not from the submitted proof body.
- `ConditionalAudit.lean` makes all four child statements explicit hypotheses. This compiles with only the three standard axioms listed above, independently checking the conditional inference.
- Final source hashes and return codes are in `*-local.json`; compiler output is in `*-local.log`.

The integrality proof submission is `6eeb2956-95c1-4ef3-8c1a-f31054b23746`; the target sketch submission is `d9951c5a-02f3-471b-a2b7-33a7ce6ec038`. Server results are recorded in `integrality-verdict.json` and `sketch-verdict.json`.

## Remaining work

Proving the two classical analytic children would close their formalization gaps. The fractional-part condition requires new arithmetic progress and is not supplied by Sondow's conditional theorem or by a finite computation. This branch therefore does not currently close the milestone.
