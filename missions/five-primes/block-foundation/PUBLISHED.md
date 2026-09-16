# Block-foundation publication record

## Published definition

| Field | Value |
| --- | --- |
| definition_name | `TaoFivePrimes_BlockFoundation` |
| definition_id | `8bca80f4-cd0c-4f05-8144-421e9d0c905e` |
| publish job_id | `e42b67b5-f7b8-4c76-985d-f23898fb6682` |
| status | **PUBLISHED** (2026-09-15T17:30:31Z) |
| mathlib_rev | `0df444a360eaa60ab8c11dca51a86af692955474` (Lean v4.33.1) |
| visibility | public |
| import path | `import Definitions.Def_TaoFivePrimes_BlockFoundation` |
| namespace | `TaoFivePrimesBlock` |

Local source: `examples/five-primes/Theorem51BlockFoundation.lean`
(20 declarations, 0 sorries, compiles in the pinned environment and
independently under `set_option autoImplicit false`).

## Why it was published

The user asked that good interim results be pushed to Prove2Me so the
platform's DAG management and lemma-reuse machinery can be used. This
file is the reusable analytic foundation of the target node
`TaoFivePrimes.theorem51_typeI_block_summation`
(`7b6bb2d9-e6fa-4629-80e7-f3a34b9ff416`): the distance-to-nearest-integer
pseudo-norm, the triangle inequality, Tao's inequality (2.1), and the
small-`d` quantitative core of (5.15).

## Contents (public API)

### §1 integer distance
- `rdist` (def)
- `rdist_eq_fract_or`, `rdist_nonneg`, `rdist_le_half`
- `abs_sin_add_int_mul_pi`, `abs_sin_neg`
- `pi_mul_fract_decomp`, `pi_mul_fract_sub_one_decomp`
- `abs_sin_pi_eq_abs_sin_pi_rdist`

### §2 inequality (2.1)
- `two_rdist_le_abs_sin` : `2 * rdist t ≤ |sin (π t)|`
- `abs_sin_le_pi_mul_rdist` : `|sin (π t)| ≤ π * rdist t`

### §3 arithmetic input of (5.15)
- `div_q_eq`, `rdist_div_ge` : `q ∤ m → 1/q ≤ rdist (m/q)`

### §4 triangle inequality
- `fract_eq_self`, `rdist_fract`, `rdist_add_eq`, `rdist_add_le_unit`
- `rdist_add_le'` : `rdist (x+y) ≤ rdist x + rdist y`
- `rdist_le_abs`, `rdist_add_le`, `rdist_sub_le_abs_sub`, `rdist_sub_abs_le_add`

### §5 small-`d` regime of (5.15)
- `d_mul_beta_le` : `|β| ≤ 1/q² ∧ 2d ≤ q → |d β| ≤ 1/(2q)`
- `rdist_d_alpha_ge` : `4α = a/q + β ∧ 2d ≤ q ∧ q ∤ ad → 1/(2q) ≤ rdist (4 d α)`

## Reuse plan

The target node imports this definition and uses:

1. `rdist_d_alpha_ge` + `two_rdist_le_abs_sin` to get
   `|sin (2π d α)| ≥ 1/q` hence `1/|sin (2π d α)| ≤ 2q` on `d ≤ q/2`
   (Tao's (5.16));
2. `rdist_add_le'` / `rdist_sub_le_abs_sub` for the block shift argument
   (5.15 applied at `d = 2jq + q/2 + m`).
