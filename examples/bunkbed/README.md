# Bunkbed Scratch Archive

The mission is complete. Use [the mission status](../../missions/bunkbed/status.md) and [the accepted standalone solution](../../Solutions/Sol_BunkbedFalse_sub_probability_grouping.lean) as the authoritative entry points.

| File | Role |
| --- | --- |
| `GroupingCore.lean` | Checked state classifier, embedding, and one-level pushforward |
| `GroupingAlgebra.lean` | Checked abstract configuration and two-level sum identities |
| `GroupingFinal.lean` | Checked final connection, importing the two scratch modules above |
| `GroupingTypecheck.lean` | Exact type comparison between the accepted solution and target mirror |
| `Push.lean` | Earlier independently checked finite-pushforward prototype |
| `GroupingDirect.lean` | Original monolithic draft; preserved unchanged, not the accepted source |
| `GroupingFinish.lean`, `GroupingFinishExplicit.lean` | Failed intermediate connection attempts; preserved for diagnosis |
| `bbfactor.lean`, `image.lean`, `partition.lean` | Downloaded reference solution sources |

Cross-imports now use `examples.bunkbed.*`. Run `scripts/check_grouping.ps1 -CheckScratch` from the workspace root to compile the successful module chain and the accepted submission. Failed drafts are intentionally excluded.

Historical logs and server JSON responses are in `missions/bunkbed/verification/`. The full old handoff is preserved at `missions/bunkbed/handoff-history.md`; paths in that historical document describe the pre-archive layout.
