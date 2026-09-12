# Prove2Me Handoff Status: The Bunkbed Conjecture Is False

Last updated: 2026-09-12 (Asia/Shanghai)

## Completed continuation (2026-09-12, 17:31)

This section supersedes the historical blocker and continuation plan below.

- The complete grouping proof now compiles locally with `autoImplicit=false` in **31.52 seconds**.
- Submission source: `Solutions/Sol_BunkbedFalse_sub_probability_grouping.lean`.
- English mathematical explanation: `Solutions/SubProbabilityGrouping.md`.
- The exact type comparison in `examples/GroupingTypecheck.lean` also compiles.
- Submitted to Prove2Me as `cbc9cab1-d2fd-4ea0-ae33-93402c2c8b82`; server verdict is **`ACCEPTED`**, timestamp `2026-09-12T17:30:22.768007+08:00`.
- Live API checks confirmed that `sub_probability_grouping`, `sub_probability_transfer`, `explicit_counterexample`, and the mission root `bunkbed_conjecture_false` are all **`Proved`**.
- The root `/open-leaves` endpoint returned **`total: 0`** and an empty list. The mission frontier addressed by this handoff is closed.
- No new public definitions or child theorems were needed. The submission imports only the four existing auxiliary theorem modules.
- The original untracked `examples/GroupingDirect.lean` is preserved as historical scratch work. Run the new solution file instead; do not mistake the old scratch file for the validated submission.

### What fixed the compiler bottleneck

The state classifier, embedding proof, one-copy mass, and one-level pushforward all compiled after isolation in `examples/GroupingCore.lean`. The two-level equivalence fixes were also verified.

The final connection now uses four separately checked algebraic helpers in `examples/GroupingAlgebra.lean`: `configuration_subset`, `push_two`, `pair_state_sum`, and `sum_indicator_congr`. `examples/GroupingFinal.lean` connects these helpers to the concrete graph. The self-contained submission combines these files and imports no scratch modules.

Crucially, the final connection marks `Fintype.piFinset` and `gadgetE` **locally irreducible**. Without this boundary, elaboration of membership hypotheses and even the constructor-name linter attempted to normalize the enormous concrete configuration space. The local attribute controls elaboration only; it introduces no axiom and does not disable kernel checking. The proof uses `maxHeartbeats 200000`, rather than the previous `2000000`.

The final sum conversion explicitly supplies the curried summand to `Fintype.sum_prod_type'`, and the two-level product calculation accounts for multiplication associativity and ordering.

### Reproduce local validation

```powershell
.\scripts\check_grouping.ps1
```

The script uses the installed pinned Lake binary directly, avoiding an unrelated elan self-update network request. It compiles the self-contained submission, compares its type with the target, and prints its local axioms. `sorryAx` in this local report comes from the platform theorem mirrors, whose bodies are placeholders. Server verification has now accepted the proof and its dependencies; the submitted source itself contains no `sorry`, custom axiom, or `native_decide`.

The submission SHA-256 is `17A3390AED50533FDC16DFC2031791205C5AD553386F1E1F7DAA7C4D94E3F1D3`.

### Final verification records

- `examples/GroupingVerdict.json`: accepted submission verdict.
- `examples/GroupingRootFrontier.json`: empty root frontier.
- `examples/GroupingResolvedChain.json`: all four statements in the resolution chain are proved.
- `examples/GroupingSubmission.log`: successful local compile, with only unused-simp-argument warnings.
- `examples/GroupingTypecheck.log`: successful exact target-type check and local axiom report.

No further submission or polling is needed for this frontier. All four imported auxiliary theorems were separately rechecked online and were `Proved` during this continuation. The server job spent about 11 minutes 49 seconds between submission and acceptance; this is distinct from the measured 31.52-second local compile.

---

## Objective

Contribute a Lean proof or proof sketch to the Prove2Me mission **The Bunkbed Conjecture is False** and advance its open frontier.

All mathematical work and Lean source should be written in English. User-facing progress reports should be in Chinese.

## Prove2Me mission state

- Mission ID: `f428c039-066f-47c4-b246-7f531b8ad8f5`
- Root theorem: `BunkbedFalse.bunkbed_conjecture_false`
- Root theorem ID: `6619f63b-95ee-4233-8741-8f51852d2990`
- Current sole open leaf, confirmed through `/open-leaves`:
  - `BunkbedFalse.sub_probability_grouping`
  - theorem ID: `a6bfde9e-efba-4ee3-a87f-0edb760aa61f`
  - status: `Open`

The platform credentials are in `credentials.json`. Never print, commit, or send its secrets anywhere except `https://prove2.me/api/v1`.

## Accepted contributions from this task

### 1. Main explicit counterexample proof sketch

- Target: `BunkbedFalse.explicit_counterexample`
- Theorem ID: `8fabe7f0-a20f-4baa-a5ac-39619039d4e4`
- Submission ID: `484ffebe-3c12-4abb-95e6-563dfe1da4ab`
- Verdict: `SKETCH_ACCEPTED`
- Local source: `Solutions/Sol_BunkbedFalse_explicit_counterexample.lean`

This sketch reduces the explicit graph counterexample to existing proved infrastructure plus the probability-transfer theorem.

### 2. Probability-transfer proof sketch

- New theorem: `BunkbedFalse.sub_probability_transfer`
- Theorem ID: `4dace61e-ea97-4cab-90d1-689e0f7562da`
- Submission ID: `f0a19b81-ad19-4ca5-8273-6c05603bddde`
- Verdict: `SKETCH_ACCEPTED`
- Local source: `Solutions/Sol_BunkbedFalse_sub_probability_transfer.lean`

It reduces transfer to:

- `BunkbedFalse.sub_gadget_copies_disjoint`
- `BunkbedFalse.sub_probability_grouping`

### 3. Direct proof that the six gadget edge copies are disjoint

- Theorem: `BunkbedFalse.sub_gadget_copies_disjoint`
- Theorem ID: `bf7853e4-0cb6-4c5f-a431-52ecc006ac8d`
- Accepted submission ID: `db4c52cd-b9fe-4f6b-8f57-e0375ec40149`
- Verdict: `ACCEPTED`
- Local source: `Solutions/Sol_BunkbedFalse_sub_gadget_copies_disjoint.lean`

The proof is pure kernel Lean. It counts the six labelled edge copies and uses the already proved total edge count `14442` to force injectivity of the forgetful map, hence pairwise disjointness.

An earlier `native_decide` attempt compiled locally but was correctly rejected by the server soundness guard:

- Rejected submission ID: `2cc24f62-5ec7-4ba9-a275-02de81dbbd2e`
- Reason: `native_decide` trusts compiled native code rather than the Lean kernel.

Do not retry that approach.

### 4. Mission communication

- Mission discussion comment ID: `a02d61a6-4c41-435b-97eb-2d5edacc7652`
- The explicit counterexample theorem was rated difficulty `9`.

## Source and mathematical reduction

Paper used:

- Gladkov, Pak, Zimin, *The bunkbed conjecture is false*
- PDF: <https://www.math.ucla.edu/~pak/papers/BunkBed4.pdf>
- Relevant construction: Section 4.2, pages 6-7

The construction uses `p = 1/2`, `n = 1204`, replaces Hollom's six hyperedges with six copies of `G_1204`, and produces a graph with `7222` vertices and `14442` edges. The remaining theorem is the formal pushforward argument identifying independent percolation configurations of those gadget copies with independent Wierman-Ziff states.

## Existing proved Prove2Me lemmas used by the remaining proof

These theorem modules may need to be mirrored locally as `Thm_*.lean` placeholders before importing them.

- `BunkbedAux.bbProb_biUnion_disjoint`
  - ID: `8e553437-46c3-46c2-9a0b-af807db09ccf`
  - status: `Proved`
  - locally mirrored at `Theorems/Thm_BunkbedAux_bbProb_biUnion_disjoint.lean`
- `BunkbedAux.probOf_image_map`
  - ID: `76e614ef-fcd0-4afd-94aa-848205d6284f`
  - status: `Proved`
  - locally mirrored at `Theorems/Thm_BunkbedAux_probOf_image_map.lean`
- `BunkbedAux.reach_image_map`
  - ID: `2fe14d4d-881c-4b23-946a-11da0e4fc040`
  - status: `Proved`
  - locally mirrored at `Theorems/Thm_BunkbedAux_reach_image_map.lean`
- `BunkbedAux.exists_unique_partition_state`
  - ID: `1220ff7d-589b-44f3-8e33-63838982b95a`
  - status: `Proved`
- `BunkbedFalse.bb_boundary_reduce`
  - ID: `5836ba26-1e39-41fd-b0c6-de053eecf8ce`
  - status: `Proved`
  - locally mirrored at `Theorems/Thm_BunkbedFalse_bb_boundary_reduce.lean`

The accepted solution sources for three auxiliary theorems were downloaded for reference:

- `examples/bbfactor.lean`
- `examples/image.lean`
- `examples/partition.lean`

They contain internal helper definitions that are not exported by the platform theorem modules. In particular, `GadgetStates.wzStateOf`, its event lemmas, and `BunkbedRelabel.emb_inj` must either be reproduced in a solution or published as reusable platform definitions/theorems.

## Work completed toward the remaining theorem

The main scratch file is:

- `examples/GroupingDirect.lean`

It currently contains the following proof components.

### State classifier and boundary characterization

- `Grouping.stateOf`
- `Grouping.state_boundary`
- `Grouping.state_event`
- `Grouping.partMass`
- `Grouping.prob_state_eq`

These establish that every edge configuration induces one of the five WZ states and that the state records exactly the three pairwise reachability facts among the attachment vertices.

### Relabelling and one-copy state mass

- `Grouping.state_image`
- `Grouping.prob_state_image`
- `Grouping.gadgetW_half`
- arithmetic proof of `Grouping.emb_inj`
- `Grouping.copy_state_mass`

These show that each embedded gadget copy has state mass `P s`, using the existing `probOf_image_map` and `reach_image_map` theorems and the five hypotheses in the target statement.

### Generic finite pushforward identity

- `Grouping.pi_pushforward_sum`
- independent smaller prototype: `examples/Push.lean`

The prototype compiles successfully with the kernel. Its statement is the reusable algebraic identity

```lean
theorem pi_pushforward_sum
    {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
    {A : I -> Type*}
    (D : forall i, Finset (A i))
    (st : forall i, A i -> B)
    (mu : forall i, A i -> Q)
    (P : I -> B -> Q)
    (hmass : forall i b, sum over a in D i with st i a = b of mu i a = P i b)
    (F : (I -> B) -> Q) :
    sum over configurations a of F (states a) * product_i mu_i(a_i)
      = sum over state functions b of F b * product_i P_i(b_i)
```

The actual Lean syntax is in `examples/Push.lean`; do not copy the ASCII pseudocode above.

### One-level pushforward and two-level pairing

- `Grouping.one_level_push`
- `Grouping.twoLevel`
- `Grouping.twoLevelEquiv`
- `Grouping.twoLevel_prod`
- `Grouping.copyStates`
- `Grouping.selected_state_match`
- `Grouping.configuration_reach`

The intended direct `solution` is also present at the end of `examples/GroupingDirect.lean`.

## Current blocker

The direct monolithic file is mathematically complete in structure, but Lean spends excessive time reducing types involving the concrete `gadgetE 1204` and repeated `Fintype.piFinset` expressions.

The most recent full compile was manually stopped after roughly 13 minutes. Before that run, the previous compile produced:

1. `twoLevelEquiv.left_inv` and `right_inv` did not unfold `twoLevel`. This has now been edited to use `simp [twoLevel]`, but the edit has not completed a full verification run.
2. `Grouping.configuration_reach` previously timed out while extracting pointwise subset facts from `Fintype.mem_piFinset`.
3. The main `solution` timed out around the reachability rewrite and pushforward steps because `simpa [D, E]` triggered expensive weak-head normalization.

The current file has `set_option maxHeartbeats 2000000`, which is too blunt and makes feedback very slow. The direct proof should be refactored into smaller compiled modules or, preferably for Prove2Me, into a proof sketch with meaningful child theorems.

## Recommended continuation strategy

Do not keep compiling the 400-line monolithic file unchanged. Split the remaining frontier into reusable public pieces so each declaration has a small type-checking boundary.

Recommended decomposition:

1. Publish and directly prove a generic theorem such as `BunkbedAux.pi_pushforward_sum` using the already compiling source in `examples/Push.lean`.
2. Publish a reusable state-classifier definition, or state the next theorem with a local `let stateOf := ...` if publishing a definition is inconvenient.
3. Add and directly prove `BunkbedFalse.sub_copy_state_mass`: for every copy `i` and state `s`, the filtered sum of configuration weights inducing `s` equals `P s`.
4. Add and directly prove `BunkbedFalse.sub_configuration_reach`: for any legal pair of per-copy configuration tuples, substituted-graph bunkbed reachability is equivalent to WZ reachability under their induced states. This should be a short wrapper around `bb_boundary_reduce` plus `state_boundary`.
5. Submit a proof sketch for `BunkbedFalse.sub_probability_grouping` importing those children. The sketch should:
   - rewrite `subEdges` with `bbProb_biUnion_disjoint`;
   - replace the reachability indicator using `sub_configuration_reach`;
   - apply `pi_pushforward_sum` once for the upper layer and once for the lower layer;
   - use the explicit equivalence between `(Fin 6 -> WZ) x (Fin 6 -> WZ)` and `Fin 6 x Fin 2 -> WZ`;
   - finish by unfolding `wzProb`.
6. Prove any remaining algebraic child directly, then poll `/open-leaves` until the root has no open leaves.

An even more compiler-friendly option is to state one generic two-layer pushforward theorem over abstract finite types. This avoids mentioning `gadgetE 1204` in the algebraic theorem entirely. Instantiate it only in the final short sketch.

## Lean performance notes

- Avoid `simp [D, E]` when `D` contains `gadgetE 1204`; it can force large concrete reductions.
- Prefer staging facts:

```lean
have hi := Fintype.mem_piFinset.mp hS i
exact Finset.mem_powerset.mp hi
```

- Prefer abstract aliases and explicit theorem arguments over `apply` when dependent types are large.
- Keep `simp only` lists narrow.
- Compile generic algebraic lemmas in separate files first.
- Do not use `native_decide` in a server submission.

## Local validation status

- `examples/Push.lean`: compiles successfully.
- `Solutions/Sol_BunkbedFalse_sub_gadget_copies_disjoint.lean`: compiles successfully and was accepted by Prove2Me.
- `Solutions/Sol_BunkbedFalse_explicit_counterexample.lean`: locally compiled as a proof sketch and was accepted by Prove2Me.
- `Solutions/Sol_BunkbedFalse_sub_probability_transfer.lean`: locally compiled as a proof sketch and was accepted by Prove2Me.
- `examples/GroupingDirect.lean`: not yet fully compiling; see blocker above.

## Submission workflow reminder

Follow `SKILL.md` and `references/mission_solver.md`.

- A submitted proof file must have a top-level theorem named exactly `solution`.
- Its type must exactly match the target theorem's formal statement.
- Never import the target theorem itself.
- Do not leave `sorry` in the submitted solution source.
- Imports of other platform theorem modules are allowed.
- Submit through `POST /api/v1/verify`, poll the returned submission ID, then add an English explanation.
- Recheck the root frontier through:

```text
GET /api/v1/theorems/6619f63b-95ee-4233-8741-8f51852d2990/open-leaves
```

No GitHub push is required for Prove2Me submission. Local Git/GitHub publication is separate and has not been done.
