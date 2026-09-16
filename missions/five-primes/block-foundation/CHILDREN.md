# Two children for `TaoFivePrimes.theorem51_typeI_block_summation`

Target: theorem `7b6bb2d9-e6fa-4629-80e7-f3a34b9ff416`
(`TaoFivePrimes.theorem51_typeI_block_summation`), currently **Open**.

The parent is a pure envelope-summing lemma: given a nonnegative `W` obeying
the pointwise Type I envelope on the positive odd `d ≤ UV`, bound
`Σ_{d ∈ theorem51Divisors U V} W d` by the two-term expression of Tao's
(5.17).

Tao's own text (`tmp/tao.txt`, Section 5.2) splits the argument into exactly
two halves, and the split is the natural one for the platform DAG:

> "We first control the contribution to (5.14) when `d ≤ q/2`. […]
> Now consider the contribution to (5.14) of a block of the form
> `2jq + q/2 < d ≤ 2(j+1)q + q/2` […]"

Only **two** children are published (the approved budget); each is genuinely
load-bearing and independently reusable.

---

## Child 1 — `TaoFivePrimes.theorem51_odd_vinogradov_min_sum`

**Status: PROVED locally, `sorry`-free**, in
`examples/five-primes/Theorem51Cor35.lean` (declarations `one_le_of_one_le_floor`,
`floor_le_of_one_le_floor`, `odd_mem_Ioc_iff`, `odd_min_sum_reindex`,
`vinogradovMinSum`, `vinogradovMinSumOdd`, `odd_vinogradov_min_sum`), and
published inside the definition `TaoFivePrimes_BlockFoundationCor35`
(job `e0f3a3d9-59ec-436e-90a9-6cc9c9221b89`).

**Statement.** Corollary 3.5 (Tao, arXiv:1201.6656v4): for `1 ≤ x`, the
odd-restricted Vinogradov min-sum with parameter `α` and phase `θ` is
bounded, and it follows from Lemma 3.4 instantiated at `(2α, πα + θ)` on the
shifted endpoints `((x−1)/2, (y−1)/2]`.

**Why it is a child.** Tao cites Corollary 3.5 as an external input for
*both* halves of the parent (the small-`d` range and every block), so without
it the parent's assembly is not even statable. The reindexing `n = 2m+1` is
the entire non-citation content of Corollary 3.5, and it is reusable in any
later use of the odd Vinogradov estimate.

**What is *not* here.** The analytic content of Lemma 3.4 (the Vinogradov
bound itself) stays a hypothesis of `odd_vinogradov_min_sum`; it is the
classical published estimate and is not re-proved.

**Two slack conditions that matter and are recorded in the Lean file.** The
index-set identity needs `1 ≤ x` (at `x = 0, y = 1` it is false), and
`Nat.floor_lt` needs an explicit `0 ≤ a` side condition. Both are satisfied
in every application because the summation starts at `d = 1`.

---

## Child 2 — `TaoFivePrimes.theorem51_typeI_block_assembly`

**Status: IN PROGRESS**, `examples/five-primes/Theorem51Assembly.lean`.

**Statement (target shape).** With the parent's hypotheses (`4 ≤ q`,
`q ⊥ a.natAbs`, `4α = a/q + β`, `|β| ≤ q⁻²`, `0 < x`, `40 ≤ U, V`,
`UV ≤ x/4`, `0 ≤ W`, and the pointwise envelope on `theorem51Divisors U V`),
prove the parent's conclusion

```
Σ_{d ∈ theorem51Divisors U V} W d
  ≤ 0.5 * (x/q) * log x * (log (2*U*V/q + 4) + 4)
    + 0.89 * (U*V + (5/2)*q) * (8 + log q) * log (2*x)
```

given Child 1.

**Sub-steps (Tao's own order).**

1. **Small-`d` contribution**, `2d ≤ q`. From `rdist_d_alpha_ge` with
   `q ∤ ad` (which follows from `q ⊥ a` and `0 < d < q`), (2.1) gives
   `1/|sin(2πdα)| ≤ 2q`. Applying Child 1 on `[−q/2, q/2]` and using
   symmetry,
   `Σ_{d ≤ q/2, odd} min(2q, 1/|sin(2πdα)|) ≤ (2/π) q log 4q + 4q`,
   so the contribution to `Σ W d` is at most
   `2 log 2 · log 2x · ((2/π) q log 4q + 4q)`.
2. **Each block** `2jq + q/2 < d ≤ 2(j+1)q + q/2`, `j ≤ UV/2q − 1/4`.
   Freeze the first alternative at the left endpoint (`freeze_x_div`), keep
   the cosecant term, apply Child 1 to the block (width `2q`, so the block
   count is `1`), and crudely bound by
   `x/(2jq+q/2) log x + 4(log 2) log 2x · ((2/π) q log 4q + 4q)`.
3. **Sum over blocks + integral test.** Every `d > q/2` lies in exactly one
   block (`exists_block_of_gt`), so
   `Σ_{d > q/2} W d ≤ Σ_{0≤j≤UV/2q−1/4} x/(2jq+q/2) log x
     + (UV/2q + 5/4)((2/π)q log 4q + 4q) · 4 log 2 · log 2x`,
   and the integral test gives
   `Σ_{0≤j} x/(2jq+q/2) ≤ (1/2q) ∫_{q/2}^{UV+2q} x/y dy
     = (x/2q) log(2UV/q + 4)`,
   the `+4` inside the logarithm being the restored `j = 0` term that the
   source's display omits.
4. **Constant rounding.** `(2/π) q log 4q + 4q ≤ (2/π) q (8 + log q)` and
   `(1/2)(2/π)(4 log 2) ≤ 0.89`; then `log 2x ≥ log x` weakens the first
   term to the platform's `0.5*(x/q)*log x*(...)`.

---

## Parent as a SKETCH reduction

Once Child 1 is published and Child 2 is at least stated with its own
sub-obligations isolated, submit the parent with a SKETCH reduction that
imports the two children and adds them. The parent then resolves
automatically when both children are Proved.

The reduction must not import the parent itself, must be `sorry`-free, and
must name its children by their platform theorem names in the `explanation`
and (where the platform supports it) in the submitted Lean.
