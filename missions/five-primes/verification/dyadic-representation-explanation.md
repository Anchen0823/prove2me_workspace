# `theorem51_typeII_dyadic_representation` — complete proof

## The statement

For `x > 0`, `U, V ≥ 40`, `U, V < x`, `U·V ≤ x/4` and `x ≤ U·V²`, writing

```
K(W) = ∑' d, ∑' w, (if U < d ∧ V < w ∧ d.Coprime 2 ∧ w.Coprime 2
                      ∧ x/(2W) ≤ d ∧ d ≤ x/W ∧ W/2 ≤ w ∧ w ≤ W
                    then (μ d : ℂ) · (g_V(w) : ℂ) · e(α d w) else 0),
```

with `g_V(w) = ∑_{b|w, b>V} Λ(b) − (1/2) log w` the centred divisor coefficient, the
node claims the three conjuncts

1. `∀ W, W ∉ Set.Icc V (x/U) → ‖K(W)‖ = 0` (support),
2. `IntegrableOn (fun W => ‖K(W)‖/W) (Set.Ioi 0)`,
3. `T_II(x,α,U,V) ≤ 4 ∫_{(0,∞)} ‖K(W)‖ dW/W`.

This is the measure-theoretic half of the source's Type II estimate: the dyadic
identity `η₀(dw/x) = 4 ∫_0^∞ 1_{x/2W ≤ d ≤ x/W} 1_{W/2 ≤ w ≤ W} dW/W` (already
available on the platform) plus an exchange of the double sum with the integral and
the triangle inequality.

## Proof (no new child is assumed)

The file is a **complete proof**, not a reduction: it inlines the locally verified
scale-sum chain (25 modules under `examples/five-primes/`, ~1 900 lines: the odd
bilinear large sieve, the Hilbert/cosecant kernel estimates, the column partition,
the dyadic reindexing, the eta₀ pairwise integral and the finite/integral bridges)
and adds the following glue, which is the only new content.

**Splitting the summand.** The platform summand is one `if` carrying both the
coefficient guard (`U < d`, `V < w`, coprimality) and the dyadic indicator; the
local chain uses the product of the two. `theorem51DyadicSummand_eq` proves the two
agree, hence `theorem51DyadicBlock_eq_tsum` identifies `K(W)` with the split form.

**Finiteness and the factor `W`.** The local kernel is the *finite* sum
`∑_{d ≤ ⌈x⌉₊} ∑_{w ≤ ⌈x⌉₊} (coefficient) · (indicator · W⁻¹)`, while the platform
summand has no `W⁻¹`. `theorem51DyadicBlock_eq_W_mul_kernel` shows

```
K(W) = W · theorem51FiniteScaleKernel x α U V W,
```

first collapsing both `tsum`s to `Finset.Icc 1 ⌈x⌉₊` (the guard forces
`d ≤ x/W ≤ x` and `w ≤ W ≤ x` under `1 ≤ W ≤ x`, so both indices lie in the
rectangle), then multiplying through and using `W · W⁻¹ = 1`.

**Support.** `theorem51DyadicBlock_zero_outside`: for `W < V` the block reduces to
`W · kernel` and `finite_scale_kernel_zero_below` kills the kernel; for `W > x/U`
we have `x/W < U`, so the guard `U < d ≤ x/W` is empty and the block vanishes
directly.

**Integrability.** `theorem51DyadicBlock_integrableOn`: on `(0,1)` both the block and
the kernel vanish (`W/2 ≤ w ≤ W < 1` cannot hold for `w ≥ 1`), so the `1/W`
singularity is erased; on `[1,x]` the identity above gives
`‖K(W)‖/W = ‖kernel W‖`; on `(x,∞)` both sides vanish again. Hence the integrand is
pointwise equal on `(0,∞)` to `‖theorem51FiniteScaleKernel‖`, which is integrable
because the chain proves `Integrable (theorem51FiniteScaleKernel x α U V)`.

**The integral inequality.** `theorem51_setIntegral_eq_interval` converts the set
integral over `(0,∞)` into the interval integral over `V..(x/U)` using the support
statement and `setIntegral_eq_integral_of_forall_compl_eq_zero`; the third conjunct
is then `theorem51TypeII_le_scale_integral`, which the local chain already proves in
the form `T_II ≤ 4 ∫_{V}^{x/U} ‖theorem51ScaleSum x α U V W‖/W dW`.

## Verification

* Local: `lake build Solutions.Sol_TaoFivePrimes_theorem51_typeII_dyadic_representation`
  compiles against `leanprover/lean4:v4.33.1` and Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`, with no `sorry` and no `axiom`.
* The file imports only `Mathlib`, the four platform `Definitions/Def_TaoFivePrimes_*`
  modules and nothing local to `examples/` (everything is inlined).
* Expected verdict: `ACCEPTED`.
