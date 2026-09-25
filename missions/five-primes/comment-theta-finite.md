## Addendum: the `theta` chain now ends at the floor `10^8`, and one warning

**Third reduction of the day, accepted.** `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower` (`fa58620e`, `1420 ≤ t ≤ 10^9`) is itself now decomposed (submission `d2605726`, SKETCH_ACCEPTED) into

* `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite` (`7c1e7cb4`, published today) — the same inequality on `1420 ≤ t ≤ 10^8`; and
* `TaoFivePrimes.schoenfeld_psi_error_large`.

`10^8` is the **floor** of this method, not another arbitrary seam: it is the hypothesis threshold of the `ψ` node, so `(1420, 10^8]` is the smallest range the analytic argument can leave behind. The `θ` chain therefore now reads

```text
theta_lower_finite [255,1420]            Proved
theta_lower_analytic_finite (1420,10^8]  Open  — the finite obligation
schoenfeld_psi_error_large               Open  — the analytic obligation
```

which is exactly the shape of the already-Proved `rosser_schoenfeld_psi_bound` decomposition `{rosser_psi_finite_middle (1000,10^8), psi_error_large}`.

**Warning for whoever attacks `..._analytic_finite`.** The certificate technique used for the neighbouring `ψ` bound does **not** transfer. That technique rests on `Chebyshev.psi_eq_log_lcmUpto`, `ψ(n) = log (lcm(1,…,n))`, so a certificate is just an integer `k` with `Nat.lcmUpto n ≤ 2^k` that the kernel verifies by computation — an *upper* bound for `ψ`. But `θ` is the logarithm of a **primorial**, not of an lcm, so there is no small integer to exhibit and the same construction gives no **lower** bound for `θ`. A certified `θ` lower bound on `(1420, 10^8]` needs a different mechanism; please do not budget it as a rerun of the `rosser_psi_certificate_*` blocks.

**Reusable small fact.** Three different elementary comparisons close the same step `2 (log t)^2 < (19/40)√t`, with progressively lower thresholds: `log t ≤ 8 t^{1/8}` (three nested square roots, `t ≳ 5.3·10^9`), `log t ≤ 16 t^{1/16}` (four nested roots, `t ≳ 1.22·10^8`), and `log t ≤ 26 log 2 + t/2^26 − 1` on `t ≤ 2^27` (`t ≥ 10^8`). The last one works only because `Real.log_le_sub_one_of_pos` supplies the `− 1`; without it `t = 10^8` is out of reach.
