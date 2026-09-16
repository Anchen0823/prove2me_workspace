# -*- coding: utf-8 -*-
"""Seed the magic-squares mission proposal with items and milestones."""
import io
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")

PROPOSAL = "c66f86f5-4921-40de-bce2-fb6564aebc67"

# (label, theorem_id) in dependency order — definitions first
REFS = [
    ("def MagicSquares", "be2f2b6a-a540-47ae-b487-ac22532a2745"),
    ("def MagicSquaresParam3", "68eaae9b-d759-4a2a-83f6-741ecdbca5f8"),
    ("center_of_order_three", "ebbc5687-663f-472d-afb6-f760546652db"),
    ("order_three_opposite_sum_eq_twice_center", "695c1fc5-a4a3-4ee4-9eda-9a132228ba46"),
    ("magic_three_param_sufficient", "665c40f1-688c-4f40-aafb-1b8d82bbeb35"),
    ("magic_three_param_necessary", "4e513d72-b4b7-419b-a0e6-dc115ee77a94"),
    ("magic_three_param_bij", "f62c9364-c183-42f8-84b8-a6ac8e72ade7"),
    ("param_three_card", "8063946a-dd43-4ff9-9107-f3e4d7cb040b"),
    ("magic_count_three_divisible (GOAL)", "393a2adc-5e8e-4847-b9c6-f7b141a5114e"),
]

MILESTONES = [
    ("MacMahon centre identity",
     "For a $3\\times3$ magic square $M$ of line sum $s$, the centre satisfies "
     "$3M_{11}=s$. Consequently $s$ is divisible by $3$ and $M_{11}=s/3$. This is "
     "the anchor of the whole parametrization: it fixes one of the nine cells "
     "from the line sum alone."),
    ("Opposite cells sum to twice the centre",
     "For every pair of centrally opposite cells of a $3\\times3$ magic square, "
     "$M_{ij}+M_{2-i,2-j}=2M_{11}$. Equivalently an order-three magic square is "
     "automatically associative with complement constant $2M_{11}$."),
    ("Parametrization is sound",
     "If $(a,c)$ satisfies $e\\le a+c\\le 3e$, $a\\le e+c$, $c\\le e+a$, then the "
     "array $M(a,c)$ with rows $(a,\\,3e-a-c,\\,c)$, $(e+c-a,\\,e,\\,e+a-c)$, "
     "$(2e-c,\\,a+c-e,\\,2e-a)$ is a magic square of line sum $3e$. The "
     "inequalities are exactly the conditions under which the truncated "
     "subtractions in $\\mathbb{N}$ do not truncate."),
    ("Parametrization is complete",
     "Every $3\\times3$ magic square of line sum $3e$ equals $M(a,c)$ for "
     "$a=M_{00}$ and $c=M_{02}$. The eight line identities determine all seven "
     "remaining cells, so a square is determined by its two top corners."),
    ("Bijection onto admissible pairs",
     "The map $M\\mapsto(M_{00},M_{02})$ is a bijection from the $3\\times3$ magic "
     "squares of line sum $3e$ onto the admissible parameter pairs; hence "
     "$M_{3}(3e)=\\mathrm{paramCount}(e)$. Requires a `Finset.card_bij` in both "
     "directions, coercing entries into `Fin (3e+1)` via the bound "
     "$M_{ij}\\le 2e$."),
    ("Cardinality of the parameter set",
     "With $p=a-e$ and $q=c-e$, admissibility is equivalent to $|p|+|q|\\le e$, the "
     "$\\ell_{1}$ ball of radius $e$ in $\\mathbb{Z}^{2}$, which contains "
     "$1+4\\sum_{k=1}^{e}k = 2e^{2}+2e+1$ lattice points. Hence "
     "$\\mathrm{paramCount}(e)=2e^{2}+2e+1$."),
]


def api(*args):
    out = subprocess.run([PY, API] + list(args), cwd=ROOT,
                         capture_output=True, text=True)
    lines = out.stdout.splitlines()
    start = 0
    for idx, ln in enumerate(lines):
        if ln.strip().startswith("{"):
            start = idx
            break
    try:
        return json.loads("\n".join(lines[start:]))
    except Exception:
        return {"_raw": out.stdout, "_err": out.stderr}


def main():
    item_ids = []
    for label, tid in REFS:
        payload = {"kind": "reference", "theorem_id": tid}
        path = os.path.join(ROOT, "missions", "magic-squares", "item-tmp.json")
        with io.open(path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False)
        res = api("post", "/mission-proposals/%s/items" % PROPOSAL, path)
        iid = res.get("id") or res.get("item_id")
        item_ids.append((label, tid, iid))
        print("%-46s -> %s" % (label, iid or res))
    with io.open(os.path.join(ROOT, "missions", "magic-squares", "proposal_items.json"),
                 "w", encoding="utf-8") as fh:
        json.dump(item_ids, fh, ensure_ascii=False, indent=1)
    print("saved proposal_items.json")


if __name__ == "__main__":
    main()
