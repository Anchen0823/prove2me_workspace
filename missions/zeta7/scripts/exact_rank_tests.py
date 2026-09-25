"""Small independent exact checks of deg det(A+XB)=rank B and infinity support."""
from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys

from exact_hankel import ROOT, parameters


def as_fraction(value):
    return Fraction(int(value.numer()), int(value.denom()))


def independent_b(s, K, zeros, exponents):
    poles = [j for j in range(1, K + 1) if j not in zeros]
    rows = []
    for i in exponents:
        row = []
        for k in exponents:
            total = Fraction(0)
            for j in poles:
                a = -j * j
                numerator = 1
                denominator = 1
                for ell, multiplicity in zeros.items():
                    numerator *= (a + ell * ell) ** (2 * multiplicity - 1)
                for ell in poles:
                    if ell != j:
                        denominator *= a + ell * ell
                total += Fraction(numerator * a ** (i + k) * j ** (s - 1), denominator)
            row.append(total)
        rows.append(row)
    return rows


def fraction_rank(matrix):
    a = [row[:] for row in matrix]
    h = len(a)
    pivot_row = 0
    for col in range(h):
        nonzero = next((r for r in range(pivot_row, h) if a[r][col]), None)
        if nonzero is None:
            continue
        a[pivot_row], a[nonzero] = a[nonzero], a[pivot_row]
        lead = a[pivot_row][col]
        for r in range(pivot_row + 1, h):
            if a[r][col]:
                factor = a[r][col] / lead
                for c in range(col, h):
                    a[r][c] -= factor * a[pivot_row][c]
        pivot_row += 1
    return pivot_row


def determinant_degree_from_values(A, B):
    h = A.nrows()
    differences = [(A + x * B).det() for x in range(h + 1)]
    degree = -1
    for k in range(h + 1):
        if differences[0]:
            degree = k
        differences = [differences[i + 1] - differences[i]
                       for i in range(len(differences) - 1)]
    return degree


def check(label, s, K, zeros, exponents):
    h = len(exponents)
    result = parameters(s, K, 0, 0, h, zeros, exponents)
    B = independent_b(s, K, zeros, exponents)
    assert all(B[i][j] == as_fraction(result["B"][i, j])
               for i in range(h) for j in range(h))
    rank = fraction_rank(B)
    direct_degree = determinant_degree_from_values(result["A"], result["B"])
    assert rank == direct_degree == result["B_rank"] == result["degree"]
    if result["infinity_threshold_L"] is not None:
        L = result["infinity_threshold_L"]
        sign = (-1) ** ((s - 1) // 2)
        g = exponents[0]
        d = 2 * sum(zeros.values())
        assert L == K - d - (s + 1) // 2 - 2 * g
        for i in range(h):
            for j in range(h):
                if i + j < L:
                    assert B[i][j] == 0
                elif i + j == L:
                    assert B[i][j] == sign
    return dict(label=label, s=s, K=K,
                zeros={str(j): m for j, m in sorted(zeros.items())},
                exponents=exponents, L=result["infinity_threshold_L"],
                predicted_rank=result["predicted_B_rank"],
                independent_fraction_rank=rank,
                degree_from_direct_determinants=direct_degree,
                degree_from_algorithm=result["degree"])


def main():
    cases = [
        ("nozeros_constant", 7, 10, {}, [0, 1]),
        ("triangle_rank_one", 7, 12, {1: 1}, [0, 1, 2, 3]),
        ("triangle_rank_three", 7, 10, {1: 1}, [0, 1, 2, 3]),
        ("boundary_full_rank", 7, 10, {1: 1}, [0, 1, 2, 3, 4]),
        ("whole_shift", 7, 12, {1: 1}, [1, 2, 3, 4]),
        ("gapped_exponents", 7, 10, {1: 1}, [0, 1, 3, 4]),
        ("zeta5_sign", 5, 10, {1: 1}, [0, 1, 2, 3]),
        ("zeta9_sign", 9, 10, {1: 1}, [0, 1, 2, 3]),
    ]
    results = [check(*case) for case in cases]
    target = ROOT / "missions/zeta7/verification/round2-rank-tests.json"
    target.write_text(json.dumps(results, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"{len(results)} independent small cases passed: {target}")


if __name__ == "__main__":
    main()
