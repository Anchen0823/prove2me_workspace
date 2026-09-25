"""Exact all-direction triangle-norm certificates for p=9, m=n, R=4.

No zeta(9) value is used.  Positive moments S_r are enclosed between an
exact rational partial sum and that sum plus a rational integral tail.
The output (B,A9) is parameterized by all integer pairs z; its unique
rational preimage W=Tz is used directly.  Minimizing the resulting
piecewise-linear norm over Z^2 is exact via 2D Gauss reduction.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys
import time

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tmp/zeta7/exact_packages"))
from flint import fmpq, fmpq_mat  # type: ignore

VERIFY = ROOT / "missions/zeta9/round6/verification"


def as_fraction(x: fmpq) -> Fraction:
    return Fraction(int(x.numer()), int(x.denom()))


def qpair(pair: list[str]) -> fmpq:
    return fmpq(int(pair[0]), int(pair[1]))


def inverse_output_map(archive: dict) -> list[list[Fraction]]:
    """T is 5-by-2; columns are preimages of B=1 and A9=1."""
    if (int(archive["p"]), int(archive["m"]), int(archive["R"])) != (
        9, int(archive["n"]), 4
    ):
        raise ValueError("requires p=9, m=n, R=4 archive")
    raw = archive["raw_monomial_vectors"]
    if len(raw) != 5 or any(len(row) != 5 for row in raw):
        raise AssertionError("expected five-by-five raw vector map")
    F = fmpq_mat([[qpair(raw[r][i]) for r in range(5)] for i in range(5)])
    rhs = fmpq_mat([[1, 0], [0, 0], [0, 0], [0, 0], [0, 1]])
    Tin = F.inv() * rhs
    if F * Tin != rhs:
        raise AssertionError("inverse output map failed exact multiplication")
    return [[as_fraction(Tin[r, j]) for j in range(2)] for r in range(5)]


def weighted_moments(n: int, cutoff: int, deadline: float) -> tuple[list[Fraction], list[Fraction]]:
    """S_r lower/upper bounds for r=0..4, exact rationals."""
    if cutoff < n + 1:
        raise ValueError("cutoff before first nonzero term")
    fac = math.factorial
    k = n + 1
    R = fmpq(
        fac(n) ** 17 * fac(3 * n + 1),
        fac(2 * n + 1) ** 10,
    )
    sums = [fmpq(0) for _ in range(5)]
    while k <= cutoff:
        if k % 32 == 0 and time.monotonic() > deadline:
            raise TimeoutError("rational moment sum exceeded per-case deadline")
        u = k * (k + n)
        power = 1
        for r in range(5):
            sums[r] += R * power
            power *= u
        if k < cutoff:
            R *= fmpq(
                k**10 * (k + 2*n + 1),
                (k - n) * (k + n + 1)**10,
            )
        k += 1
    lows = [as_fraction(s) for s in sums]
    highs = []
    for r, lower in enumerate(lows):
        exponent = 7*n + 8 - 2*r
        if exponent <= 0:
            raise AssertionError("tail exponent must be positive")
        tail = Fraction(
            2**r * fac(n)**7 * (cutoff + 2*n)**(2*n),
            exponent * cutoff**(exponent + 2*n),
        )
        highs.append(lower + tail)
    return lows, highs


def inner(v: tuple[int, int], w: tuple[int, int], Q: tuple[Fraction, Fraction, Fraction]) -> Fraction:
    a, b, c = Q
    return a*v[0]*w[0] + b*(v[0]*w[1] + v[1]*w[0]) + c*v[1]*w[1]


def nearest_integer(x: Fraction) -> int:
    q = x.numerator // x.denominator
    return q + int(x - q > Fraction(1, 2))


def gauss_reduce(Q: tuple[Fraction, Fraction, Fraction]) -> tuple[tuple[int, int], tuple[int, int]]:
    g1, g2 = (1, 0), (0, 1)
    for _ in range(10000):
        A, B = inner(g1, g1, Q), inner(g2, g2, Q)
        if B < A:
            g1, g2 = g2, g1
            continue
        m = nearest_integer(inner(g1, g2, Q) / A)
        if m:
            g2 = (g2[0] - m*g1[0], g2[1] - m*g1[1])
            continue
        if abs(inner(g1, g2, Q)) > A / 2:
            raise AssertionError("unreduced Gauss basis")
        if abs(g1[0]*g2[1] - g1[1]*g2[0]) != 1:
            raise AssertionError("Gauss transform not unimodular")
        return g1, g2
    raise RuntimeError("Gauss reduction failed to terminate")


def norm(weights: list[Fraction], T: list[list[Fraction]], z: tuple[int, int]) -> Fraction:
    return sum(
        (weight * abs(row[0]*z[0] + row[1]*z[1]) for weight, row in zip(weights, T)),
        start=Fraction(),
    )


def form_Q(weights: list[Fraction], T: list[list[Fraction]]) -> tuple[Fraction, Fraction, Fraction]:
    return (
        sum((w*w*row[0]*row[0] for w, row in zip(weights, T)), Fraction()),
        sum((w*w*row[0]*row[1] for w, row in zip(weights, T)), Fraction()),
        sum((w*w*row[1]*row[1] for w, row in zip(weights, T)), Fraction()),
    )


def best_integer_x(
    y: int,
    g1: tuple[int, int],
    g2: tuple[int, int],
    T: list[list[Fraction]],
    weights: list[Fraction],
    require_zeta9_coefficient: bool,
) -> tuple[Fraction, tuple[int, int], int] | None:
    """Convex piecewise-linear x slice: minima sit by breakpoints."""
    candidates = {0, -1, 1}
    for row in T:
        a = row[0]*g1[0] + row[1]*g1[1]
        b = row[0]*g2[0] + row[1]*g2[1]
        if a:
            point = -b*y/a
            floor = point.numerator // point.denominator
            candidates.update((floor-1, floor, floor+1, floor+2))
    best = None
    for x in candidates:
        z = (x*g1[0] + y*g2[0], x*g1[1] + y*g2[1])
        if z == (0, 0):
            continue
        if require_zeta9_coefficient and z[1] == 0:
            continue
        value = norm(weights, T, z)
        if best is None or value < best[0]:
            best = (value, z, x)
    return best


def exact_minimum(
    weights: list[Fraction],
    T: list[list[Fraction]],
    require_zeta9_coefficient: bool,
    deadline: float,
) -> dict:
    Q = form_Q(weights, T)
    if Q[0] <= 0 or Q[2] <= 0 or Q[0]*Q[2]-Q[1]*Q[1] <= 0:
        raise AssertionError("weighted inverse map is not positive definite")
    g1, g2 = gauss_reduce(Q)
    seed = [
        z for z in (g1, g2, (g1[0]+g2[0], g1[1]+g2[1]), (g1[0]-g2[0], g1[1]-g2[1]))
        if not require_zeta9_coefficient or z[1] != 0
    ]
    if not seed:
        raise AssertionError("no seed outside pure-constant direction")
    bound = min(norm(weights, T, z) for z in seed)
    A = inner(g1, g1, Q)
    cross = inner(g1, g2, Q)
    residual = inner(g2, g2, Q) - cross*cross/A
    ratio = bound*bound/residual
    ymax = math.isqrt(ratio.numerator // ratio.denominator)
    best = None
    count = 0
    for y in range(-ymax, ymax + 1):
        if time.monotonic() > deadline:
            raise TimeoutError("two-dimensional exact minimum exceeded per-case deadline")
        candidate = best_integer_x(y, g1, g2, T, weights, require_zeta9_coefficient)
        count += 1
        if candidate is None:
            continue
        if best is None or candidate[0] < best[0]:
            best = candidate
    if best is None:
        raise AssertionError("no nonzero integer output")
    value, z, x = best
    if math.gcd(*z) != 1:
        raise AssertionError("a shortest nonzero output should be primitive")
    return {
        "value": value,
        "output_B_A9": z,
        "gauss_g1": g1,
        "gauss_g2": g2,
        "ymax": ymax,
        "y_slices_checked": count,
        "pure_constant": z[1] == 0,
    }


def decimal_string(x: Fraction) -> str:
    with localcontext() as context:
        context.prec = 40
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def exact_summary(x: Fraction) -> dict:
    num, den = str(x.numerator), str(x.denominator)
    return {
        "decimal_40_digits_noncertifying": decimal_string(x),
        "above_one_exact": x > 1,
        "below_one_exact": x < 1,
        "numerator_digits": len(num.lstrip("-")),
        "denominator_digits": len(den),
        "fraction_sha256": hashlib.sha256((num + "/" + den).encode()).hexdigest(),
    }


def exact_pair(x: Fraction) -> list[str]:
    return [str(x.numerator), str(x.denominator)]


def run(archive_path: Path, cutoff: int, deadline: float) -> dict:
    with gzip.open(archive_path, "rt", encoding="utf-8") as stream:
        archive = json.load(stream)
    n = int(archive["n"])
    T = inverse_output_map(archive)
    lows, highs = weighted_moments(n, cutoff, deadline)
    rows = []
    exact_rows = []
    for label, weights in (("lower", lows), ("upper", highs)):
        Q = form_Q(weights, T)
        g1, g2 = gauss_reduce(Q)
        n1, n2 = norm(weights, T, g1), norm(weights, T, g2)
        detQ = Q[0]*Q[2] - Q[1]*Q[1]
        exact_rows.append({
            "weights": label,
            "moment_weights": [exact_pair(w) for w in weights],
            "gram_Q_entries_Q00_Q01_Q11": [exact_pair(q) for q in Q],
            "gram_det_covolume_squared": exact_pair(detQ),
            "gauss_g1": g1,
            "gauss_g2": g2,
            "gauss_triangle_norm_g1": exact_pair(n1),
            "gauss_triangle_norm_g2": exact_pair(n2),
        })
        for exclude_pure in (False, True):
            result = exact_minimum(weights, T, exclude_pure, deadline)
            value = result.pop("value")
            rows.append({
                "weights": label,
                "exclude_pure_constant": exclude_pure,
                "min": exact_summary(value),
                "gauss_g1_triangle_norm": exact_summary(n1),
                "gauss_g2_triangle_norm": exact_summary(n2),
                "gauss_shape_ratio_N2_over_N1": decimal_string(n2/n1),
                "gram_covolume_squared": exact_summary(detQ),
                **result,
            })
    exact_payload = {
        "archive_sha256": hashlib.sha256(archive_path.read_bytes()).hexdigest(),
        "n": n,
        "cutoff": cutoff,
        "inverse_output_T_rows": [
            [exact_pair(x) for x in row] for row in T
        ],
        "moments": [
            {"r": r, "lower": exact_pair(lo), "upper": exact_pair(hi),
             "tail": exact_pair(hi-lo)}
            for r, (lo, hi) in enumerate(zip(lows, highs))
        ],
        "gram_and_gauss": exact_rows,
        "minima": [
            {
                "weights": row["weights"],
                "exclude_pure_constant": row["exclude_pure_constant"],
                "output_B_A9": row["output_B_A9"],
                "minimum": exact_pair(
                    norm(
                        lows if row["weights"] == "lower" else highs,
                        T,
                        tuple(row["output_B_A9"]),
                    )
                ),
            }
            for row in rows
        ],
    }
    return {
        "status": "exact_rational_all_direction_triangle_certificate",
        "archive": str(archive_path),
        "archive_sha256": hashlib.sha256(archive_path.read_bytes()).hexdigest(),
        "n": n,
        "cutoff": cutoff,
        "moment_bound_proof": (
            "S_r=sum_{k>n} R_n(k)u(k)^r. Partial sum k<=T is exact rational. "
            "For k>T, R_n(k)<=n!^7(1+2n/T)^(2n)k^(-7n-9), "
            "u(k)^r<=2^r k^(2r), and integral comparison gives the saved tail."
        ),
        "moment_lower_upper": [
            {"r": r, "lower": exact_summary(lo), "upper": exact_summary(hi),
             "tail": exact_summary(hi-lo)}
            for r, (lo,hi) in enumerate(zip(lows, highs))
        ],
        "T_inverse_output_coefficients_sha256": hashlib.sha256(
            repr(T).encode()
        ).hexdigest(),
        "minima": rows,
        "interpretation": (
            "min_lower>1 rules out only triangle/positive-upper certification, "
            "not a smaller true primitive form from cancellation. "
            "min_upper<1 gives an explicit direction whose triangle bound is <1."
        ),
        "__exact_payload": exact_payload,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--cutoff", type=int)
    parser.add_argument("--max-seconds", type=float, default=120)
    args = parser.parse_args()
    with gzip.open(args.archive, "rt", encoding="utf-8") as stream:
        header = json.load(stream)
    n = int(header["n"])
    cutoff = args.cutoff if args.cutoff is not None else max(256, 8*n)
    started = time.monotonic()
    result = run(args.archive, cutoff, started + args.max_seconds)
    exact_payload = result.pop("__exact_payload")
    result["elapsed_seconds"] = time.monotonic() - started
    VERIFY.mkdir(parents=True, exist_ok=True)
    path = VERIFY / f"analytic-triangle-n{n}.json"
    path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    exact_path = VERIFY / f"analytic-triangle-exact-n{n}.json.gz"
    with gzip.open(exact_path, "wt", encoding="utf-8") as stream:
        json.dump(exact_payload, stream, separators=(",", ":"))
    print(f"wrote {path}; elapsed={result['elapsed_seconds']:.3f}s")
    print(f"exact companion {exact_path}")
    for row in result["minima"]:
        print(
            f"{row['weights']} exclude_pure={row['exclude_pure_constant']}"
            f" min≈{row['min']['decimal_40_digits_noncertifying']}"
            f" z={row['output_B_A9']} ymax={row['ymax']}"
        )


if __name__ == "__main__":
    main()
