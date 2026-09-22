#!/usr/bin/env python3
"""Finite test for a proposed permutation-boundary Euler identity.

For a board C, let a(C) be the Boolean-subset Mobius coefficient of the
predicate "C contains a permutation support".  This tests

  sum_{B \\ phi <= C <= B, D <= C} a(C) = a(B) if phi <= D, else 0,

where B and D are realizable *positive* exact supports (equivalently here,
nonempty matching-covered boards) and phi is a permutation support in B.
The n <= 3 part is exhaustive.  The n = 4 part is a fixed, explicitly
recorded 600-case sample.  It is an experiment, never a proof for all n.
"""
from __future__ import annotations

import itertools
import json
import random
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "missions" / "magic-squares-v" / "research" / "2026-09-22-reciprocity" / "permutation-boundary-euler-experiment.json"


def board_label(n: int, board: int) -> str:
    width = (n * n + 3) // 4
    return f"0x{board:0{width}x}"


def permutation_masks(n: int) -> list[int]:
    masks: list[int] = []
    for perm in itertools.permutations(range(n)):
        mask = 0
        for row, col in enumerate(perm):
            mask |= 1 << (row * n + col)
        masks.append(mask)
    return masks


def coefficients(n: int) -> tuple[list[int], list[int]]:
    """Return f and its Boolean Mobius transform a, as in check_support_euler."""
    edge_count = n * n
    f = bytearray(1 << edge_count)
    for matching in permutation_masks(n):
        f[matching] = 1
    for bit in range(edge_count):
        step = 1 << bit
        for board in range(1 << edge_count):
            if board & step and f[board ^ step]:
                f[board] = 1
    a = [int(value) for value in f]
    for bit in range(edge_count):
        step = 1 << bit
        for board in range(1 << edge_count):
            if board & step:
                a[board] -= a[board ^ step]
    return list(f), a


def matching_covered(board: int, matchings: list[int]) -> bool:
    """Positive exact semi-magic supports in this finite bipartite setting."""
    if board == 0:
        return False
    covered = 0
    for matching in matchings:
        if matching & ~board == 0:
            covered |= matching
    return covered == board


def boundary_sum(B: int, phi: int, D: int, a: list[int]) -> int:
    """Sum a(C) over fiberCandidates B phi that also contain D."""
    required = (B & ~phi) | D
    optional = B & ~required
    total = 0
    sub = optional
    while True:
        total += a[required | sub]
        if sub == 0:
            return total
        sub = (sub - 1) & optional


def check_case(B: int, phi: int, D: int, a: list[int]) -> dict[str, int | bool]:
    actual = boundary_sum(B, phi, D, a)
    phi_in_D = phi & ~D == 0
    expected = a[B] if phi_in_D else 0
    return {
        "B": B,
        "phi": phi,
        "D": D,
        "actual": actual,
        "expected": expected,
        "phi_subset_D": phi_in_D,
        "passes": actual == expected,
    }


def serialise_case(n: int, case: dict[str, int | bool]) -> dict[str, int | str | bool]:
    return {
        "B": board_label(n, int(case["B"])),
        "phi": board_label(n, int(case["phi"])),
        "D": board_label(n, int(case["D"])),
        "actual": int(case["actual"]),
        "expected": int(case["expected"]),
        "phi_subset_D": bool(case["phi_subset_D"]),
        "passes": bool(case["passes"]),
    }


def exhaustive_order(n: int) -> dict[str, object]:
    matchings = permutation_masks(n)
    _, a = coefficients(n)
    supported = [B for B in range(1 << (n * n)) if matching_covered(B, matchings)]
    cases = 0
    failures: list[dict[str, int | str | bool]] = []
    pairs = 0
    for B in supported:
        for phi in matchings:
            if phi & ~B:
                continue
            pairs += 1
            for D in supported:
                if D & ~B:
                    continue
                cases += 1
                result = check_case(B, phi, D, a)
                if not result["passes"]:
                    failures.append(serialise_case(n, result))
    return {
        "n": n,
        "mode": "exhaustive",
        "positive_realizable_support_count": len(supported),
        "board_permutation_pair_count": pairs,
        "case_count": cases,
        "failure_count": len(failures),
        "counterexamples": failures,
    }


def sampled_order_four(target: int = 600, seed: int = 20260922) -> dict[str, object]:
    n = 4
    matchings = permutation_masks(n)
    _, a = coefficients(n)
    supported = [B for B in range(1 << 16) if matching_covered(B, matchings)]
    rng = random.Random(seed)
    selected: set[tuple[int, int, int]] = set()
    samples: list[dict[str, int | str | bool]] = []
    while len(samples) < target:
        B = supported[rng.randrange(len(supported))]
        phis = [phi for phi in matchings if phi & ~B == 0]
        Ds = [D for D in supported if D & ~B == 0]
        phi = phis[rng.randrange(len(phis))]
        D = Ds[rng.randrange(len(Ds))]
        triple = (B, phi, D)
        if triple in selected:
            continue
        selected.add(triple)
        samples.append(serialise_case(n, check_case(B, phi, D, a)))
    failures = [case for case in samples if not case["passes"]]
    return {
        "n": n,
        "mode": "deterministic_sample",
        "seed": seed,
        "positive_realizable_support_count": len(supported),
        "sample_target": target,
        "case_count": len(samples),
        "failure_count": len(failures),
        "counterexamples": failures,
        "samples": samples,
    }


def main() -> None:
    orders = [exhaustive_order(n) for n in (1, 2, 3)]
    orders.append(sampled_order_four())
    failures = sum(int(order["failure_count"]) for order in orders)
    payload = {
        "purpose": "Finite test of a proposed permutation-boundary Euler identity; not a general proof.",
        "coefficient": "a(C) = sum_{E subseteq C} (-1)^(|C|-|E|) HasPerm(E), using the Boolean Mobius transform from check_support_euler.py.",
        "identity": "sum_{C: B\\phi subseteq C subseteq B, D subseteq C} a(C) = a(B) if phi subseteq D, and 0 otherwise.",
        "scope": "B and D range over nonempty matching-covered boards, used here as the finite model of positive realizable exact supports; phi ranges over permutation supports contained in B. The empty support is deliberately excluded because the exact-support split is a positive-line-sum recurrence.",
        "orders": orders,
        "total_cases": sum(int(order["case_count"]) for order in orders),
        "total_failures": failures,
        "all_checked_cases_pass": failures == 0,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)}")
    for order in orders:
        print(f"n={order['n']} mode={order['mode']} cases={order['case_count']} failures={order['failure_count']}")
    print(f"total_cases={payload['total_cases']} total_failures={failures}")


if __name__ == "__main__":
    main()
