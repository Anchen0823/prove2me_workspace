#!/usr/bin/env python3
"""Finite check of the Boolean support Euler/Mobius identity for n <= 4.

For an n-by-n board B, f(B) is one exactly when B contains a perfect matching.
The subset Mobius transform of f is

    a(B) = sum_{C subseteq B} (-1)^(|B|-|C|) f(C).

This script checks the proposed support formula on every board through n = 4.
It is an experiment, not a proof for arbitrary n.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "missions" / "magic-squares-v" / "research" / "2026-09-22-reciprocity" / "support-euler-experiment.json"


def perfect_matching_masks(n: int) -> list[int]:
    """Masks of the n! permutation supports in row-major edge order."""
    masks: list[int] = []
    for perm in itertools.permutations(range(n)):
        mask = 0
        for row, col in enumerate(perm):
            mask |= 1 << (row * n + col)
        masks.append(mask)
    return masks


def component_count(n: int, board: int) -> int:
    """Number of connected components of the bipartite graph of a board.

    Matching-covered boards have a perfect matching, hence no isolated vertices;
    nevertheless the implementation handles every board directly.
    """
    vertices = 2 * n
    adjacency = [0] * vertices
    for row in range(n):
        for col in range(n):
            if board & (1 << (row * n + col)):
                left, right = row, n + col
                adjacency[left] |= 1 << right
                adjacency[right] |= 1 << left
    unseen = (1 << vertices) - 1
    components = 0
    while unseen:
        components += 1
        frontier = unseen & -unseen
        unseen ^= frontier
        while frontier:
            vertex_bit = frontier & -frontier
            frontier ^= vertex_bit
            vertex = vertex_bit.bit_length() - 1
            new = adjacency[vertex] & unseen
            unseen ^= new
            frontier |= new
    return components


def board_label(n: int, board: int) -> str:
    """Stable compact representation for counterexample records."""
    width = (n * n + 3) // 4
    return f"0x{board:0{width}x}"


def run_order(n: int) -> dict[str, object]:
    edge_count = n * n
    board_count = 1 << edge_count
    matching_masks = perfect_matching_masks(n)

    # f starts as the indicator of a permutation support.  Boolean subset-zeta
    # propagation makes it the indicator that a board contains some matching.
    f = bytearray(board_count)
    for matching in matching_masks:
        f[matching] = 1
    for bit in range(edge_count):
        step = 1 << bit
        for board in range(board_count):
            if board & step and f[board ^ step]:
                f[board] = 1

    # In-place subset Mobius transform.  Values remain small signed integers.
    a = [int(value) for value in f]
    for bit in range(edge_count):
        step = 1 << bit
        for board in range(board_count):
            if board & step:
                a[board] -= a[board ^ step]

    matching_board_count = 0
    matching_covered_count = 0
    nonmatching_nonzero: list[dict[str, object]] = []
    covered_formula_failures: list[dict[str, object]] = []
    full = board_count - 1

    for board in range(board_count):
        covered_edges = 0
        if f[board]:
            matching_board_count += 1
            for matching in matching_masks:
                if matching & ~board == 0:
                    covered_edges |= matching
        matching_covered = board != 0 and covered_edges == board
        if matching_covered:
            matching_covered_count += 1
            components = component_count(n, board)
            exponent = board.bit_count() - 2 * n + components
            expected = -1 if exponent % 2 else 1
            if a[board] != expected:
                covered_formula_failures.append({
                    "board": board_label(n, board),
                    "edges": board.bit_count(),
                    "components": components,
                    "exponent": exponent,
                    "actual": a[board],
                    "expected": expected,
                })
        elif a[board] != 0:
            nonmatching_nonzero.append({
                "board": board_label(n, board),
                "edges": board.bit_count(),
                "actual": a[board],
                "contains_perfect_matching": bool(f[board]),
                "covered_edges": board_label(n, covered_edges),
            })

    return {
        "n": n,
        "edge_count": edge_count,
        "board_count": board_count,
        "perfect_matching_count": len(matching_masks),
        "boards_containing_perfect_matching": matching_board_count,
        "matching_covered_nonempty_boards": matching_covered_count,
        "full_board": {
            "board": board_label(n, full),
            "coefficient": a[full],
            "components": component_count(n, full),
            "expected": -1 if ((edge_count - 2 * n + component_count(n, full)) % 2) else 1,
        },
        "nonmatching_boards_with_nonzero_coefficient": nonmatching_nonzero,
        "matching_covered_formula_counterexamples": covered_formula_failures,
    }


def main() -> None:
    orders = [run_order(n) for n in range(1, 5)]
    payload = {
        "purpose": "Finite n<=4 check of a proposed Boolean Mobius support identity; not a proof.",
        "definition": "a(B) = sum_{C subseteq B} (-1)^(|B|-|C|) f(C), where f(B) means B contains a perfect matching.",
        "matching_covered": "nonempty B whose every edge belongs to at least one perfect matching contained in B",
        "claimed_pattern": "a(B)=0 for non-matching-covered B; for matching-covered B, a(B)=(-1)^(|B|-2n+c(B)).",
        "orders": orders,
        "all_checks_pass": all(
            not order["nonmatching_boards_with_nonzero_coefficient"]
            and not order["matching_covered_formula_counterexamples"]
            for order in orders
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)}")
    for order in orders:
        print(
            "n={n} matchings={perfect_matching_count} supports={matching_covered_nonempty_boards} "
            "full={full_board[coefficient]} noncovered_counterexamples={nonmatching} "
            "covered_counterexamples={covered}".format(
                n=order["n"],
                perfect_matching_count=order["perfect_matching_count"],
                matching_covered_nonempty_boards=order["matching_covered_nonempty_boards"],
                full_board=order["full_board"],
                nonmatching=len(order["nonmatching_boards_with_nonzero_coefficient"]),
                covered=len(order["matching_covered_formula_counterexamples"]),
            )
        )
    print(f"all_checks_pass={payload['all_checks_pass']}")


if __name__ == "__main__":
    main()
