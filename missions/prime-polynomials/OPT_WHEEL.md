# Incremental wheel through 17

`opt_wheel17_search.cpp` preserves the exception-aware target filter, distinct absolute prime scan, and constant interval [-498960, 501269]. It constructs allowed residues incrementally modulo 2*3*5*7*11*13*17 = 510510 instead of repeatedly testing all constants surviving a 2310 wheel. At each step, every residue r modulo m lifts uniquely to r+k*m for k=0,...,p-1; retain it iff the polynomial has no root for that constant modulo p. Thus this transformation exactly enumerates the original root-free residues through 17. Primes 19 and 23 remain checked afterward, and the exception logic is unchanged. Loop k outside r maintains sorted order without sorting, preserving original constant scan order.

No additional number-theoretic exclusions are introduced. This file targets lengths 47/50 as in the existing campaign; it is NOT a general target-45 implementation.

Correctness: 51,051,000 residue equivalence checks over 100 random shapes, zero mismatches; existing 150,000 exception tests, zero false negatives; known 49-term fixture passes. Three repeated benchmark pairs for each family have identical passed23/scanned counts and byte-identical improvement JSONL logs.

Same-machine full-program medians (including initialization), seed 20260924:
- Cubic mode 3, 50,000 shapes: 1.67953 s -> 0.677015 s, 2.4808x; 1,800,735 passed23 and 2,587 scans in both versions.
- Quintic mode 8, 10,000 shapes, mutation radius 50: 1.76099 s -> 1.50576 s, 1.1695x; 514,930 passed23 and 1,155 scans in both versions.

Build: `g++ -O3 -std=c++17 missions/prime-polynomials/scripts/opt_wheel17_search.cpp -o tmp/prime-polynomial-build/opt_wheel17_search.exe`
Regression: build and run `scripts/opt_test_wheel.cpp` identically.
Benchmark arguments: `3 40 20260924 PREFIX 50000 exception 50` and `8 40 20260924 PREFIX 10000 exception 50`; use `exception_search.cpp` for baseline. Detailed times: verification/opt-wheel-summary.json. Intermediate wheel-through-13 experiment remains in opt_wheel_search.cpp; through-17 is preferred.

Completion reporting retains completed_shapes, budget_seconds and termination_reason. Only full constant scans increment completed_shapes; shapes ruled out by the residue prefilter are completed immediately.
