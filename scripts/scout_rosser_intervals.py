"""Numerical scouting only. Floating-point output is NOT a Lean certificate."""
import argparse
import bisect
import json
import math
import time
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("--limit", type=int, default=99_999_999)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
started = time.perf_counter()
limit = args.limit
if limit < 1000:
    raise ValueError("Use a limit of at least 1000")
prime = bytearray(b"\x01") * (limit + 1)
prime[:2] = b"\x00\x00"
for p in range(2, math.isqrt(limit) + 1):
    if prime[p]:
        prime[p*p:limit+1:p] = b"\x00" * ((limit - p*p)//p + 1)
powers = []
for p in range(2, math.isqrt(limit) + 1):
    if prime[p]:
        q = p*p
        while q <= limit:
            powers.append((q, math.log(p)))
            q *= p
powers.sort()
intervals = []
a = 1
while a <= limit:
    b = a if a <= 1000 else min(limit, a + max(1, a//100))
    intervals.append([a, b])
    a = b+1
psi = 0.0
correction = 0.0
power_index = 0
next_prime = prime.find(1, 2)
max_ratio = [0.0, 1]
checks = []
for a, b in intervals:
    while True:
        power_n = powers[power_index][0] if power_index < len(powers) else limit+1
        p = next_prime if next_prime >= 0 else limit+1
        n = min(p, power_n)
        if n > b:
            break
        if p < power_n:
            value = math.log(p)
            next_prime = prime.find(1, p+1)
        else:
            value = powers[power_index][1]
            power_index += 1
        # Kahan summation reduces rounding error; it is still not a proof.
        value -= correction
        total = psi + value
        correction = (total - psi) - value
        psi = total
        if psi/n > max_ratio[0]:
            max_ratio = [psi/n, n]
    gap = 1.03883*a - psi
    checks.append({"a": a, "b": b, "psi_b_approx": psi, "gap_approx": gap})
result = {
    "status": "numerical_scout_only",
    "limit": limit,
    "interval_count": len(checks),
    "failed_intervals": [c for c in checks if c["gap_approx"] <= 0],
    "minimum_gap": min(checks, key=lambda c: c["gap_approx"]),
    "maximum_psi_ratio_approx": max_ratio[0],
    "maximum_psi_ratio_at": max_ratio[1],
    "seconds": time.perf_counter()-started,
    "checks": checks,
}
args.output.write_text(json.dumps(result, indent=2), encoding="utf-8")
print(json.dumps({k:v for k,v in result.items() if k != "checks"}, indent=2))
