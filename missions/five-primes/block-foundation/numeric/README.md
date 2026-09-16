# Numeric verification for the Type I block summation

These are throwaway probes used to decide the *maths* of
`theorem51_typeI_block_summation` before committing to a Lean proof.  They are
kept because two of them overturned earlier wrong conclusions, and because the
same sweeps are needed again if the constants are ever re-derived.

Run with the managed interpreter:

```
C:/Users/anche/.workbuddy/binaries/python/versions/3.13.12/python.exe <script>
```

Everything is `math`-only (no numpy/sympy needed).

## The decisive ones

| script | what it settles |
| --- | --- |
| `probe_max2.py` | sweeps the **admissible** region (`U,V ≥ 40`, `UV ≤ x/4`) and gives `max(envelope / platform-RHS) = 0.44`.  This is the reason the parent node is *not* over-strong. |
| `probe_mech.py` | checks Tao's per-block RHS `X_j + 2C + (2/π)Cq log 4q` on every block: 0 violations over 12501/5001/501 blocks at `q = 4/10/100`. |
| `probe_decomp.py` | verifies the sharp count-1 form `2X_j + (2/π)Cq log 4q` (max `s/rhs = 0.60…0.76`). |
| `probe_count.py` | shows the published count `⌊2q/(2q)⌋ + 1 = 2` over-counts the width-`2q` block, whose odd `d` number only `q`. |
| `probe_sanity.py` | proves the adversarial case is `α = 1/(4q)`, where the `B`-alternative *never* wins on the block range. |

## The trap (do not repeat)

`probe_admissible.py`, `probe_verdict.py` and `probe_ce.py` are the scripts that
produced the **wrong** "the statement is false, overshoot grows like `q`"
conclusion.  They evaluate the envelope at `x` astronomically larger than
`4·UV` (e.g. `x = 10¹²`, `UV = 1600`).  At such a point the phase
`sin(π d/(2q))` is generic across the short `d`-range, `B` dominates, the sum
collapses, and dividing by a target that still carries the `x`-scaled `1/q`
gives a meaningless large ratio.

**Rule: always sweep `U ∈ [40, …]`, `V ∈ [40, …]` with `UV ≤ x/4` held, and
vary `x` over a *bounded multiple* of `UV` (see `probe_max2.py`'s
`xmul ∈ {1, 10, 100, 1000}`), never an unbounded one.**
