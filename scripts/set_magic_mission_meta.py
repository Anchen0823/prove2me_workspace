# -*- coding: utf-8 -*-
"""Set the mission goal, item order and milestone list on the proposal."""
import io
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")

PROPOSAL = "c66f86f5-4921-40de-bce2-fb6564aebc67"

# item_id from proposal_items.json, in reading/attack order
ORDER = [
    "182d898c-fb5d-4250-be1f-0f8d64fe0d3d",  # def MagicSquares
    "39206e13-f3e7-43ff-8fdd-cc5fbb9a28ce",  # def MagicSquaresParam3
    "5c25dcb7-88f0-4a61-a0d9-7035602d3036",  # center_of_order_three
    "9c7590ea-20c1-4dfb-8f99-e1c7b27e56b7",  # opposite sum
    "3362a1e7-4ed9-446c-88ff-9a6988efa9c5",  # sufficient
    "5aaca2ee-dbe6-429e-b061-518aaf16a004",  # necessary
    "2445e7be-f0cb-41a1-b0d2-3eca5ee7b577",  # bij
    "6a4132b8-befa-4132-a5ed-bbbc880fcab9",  # card
    "1deef7f3-752a-4c8f-8c59-4f6f8c9f33cd",  # GOAL
]

MAIN = "1deef7f3-752a-4c8f-8c59-4f6f8c9f33cd"

MILESTONES = [
    ("5c25dcb7-88f0-4a61-a0d9-7035602d3036",
     "MacMahon centre identity",
     "For a $3\\times3$ magic square $M$ of line sum $s$, the centre satisfies "
     "$3M_{11}=s$; in particular $3\\mid s$ and $M_{11}=s/3$. This anchors the "
     "parametrization: it fixes one of the nine cells from the line sum alone."),
    ("9c7590ea-20c1-4dfb-8f99-e1c7b27e56b7",
     "Opposite cells sum to twice the centre",
     "For every pair of centrally opposite cells of a $3\\times3$ magic square, "
     "$M_{ij}+M_{2-i,2-j}=2M_{11}$. Equivalently, an order-three magic square is "
     "automatically associative with complement constant $2M_{11}$."),
    ("3362a1e7-4ed9-446c-88ff-9a6988efa9c5",
     "Parametrization is sound",
     "If $(a,c)$ satisfies $e\\le a+c\\le 3e$, $a\\le e+c$ and $c\\le e+a$, then "
     "the array with rows $(a,\\,3e-a-c,\\,c)$, $(e+c-a,\\,e,\\,e+a-c)$, "
     "$(2e-c,\\,a+c-e,\\,2e-a)$ is a magic square of line sum $3e$. These "
     "inequalities are exactly the conditions under which the truncated "
     "subtractions in $\\mathbb{N}$ do not truncate."),
    ("5aaca2ee-dbe6-429e-b061-518aaf16a004",
     "Parametrization is complete",
     "Every $3\\times3$ magic square of line sum $3e$ equals that array for "
     "$a=M_{00}$ and $c=M_{02}$: the eight line identities determine all seven "
     "remaining cells, so the square is determined by its two top corners."),
    ("2445e7be-f0cb-41a1-b0d2-3eca5ee7b577",
     "Bijection onto admissible pairs",
     "The map $M\\mapsto(M_{00},M_{02})$ is a bijection from the $3\\times3$ magic "
     "squares of line sum $3e$ onto the admissible parameter pairs, whence "
     "$M_{3}(3e)=\\mathrm{paramCount}(e)$. This needs a `Finset.card_bij` in both "
     "directions, coercing entries into `Fin (3e+1)` using $M_{ij}\\le 2e$."),
    ("6a4132b8-befa-4132-a5ed-bbbc880fcab9",
     "Cardinality of the parameter set",
     "Substituting $p=a-e$ and $q=c-e$, admissibility becomes $|p|+|q|\\le e$: the "
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
        return {"_raw": out.stdout[:600], "_err": out.stderr[:300]}


def main():
    # 1. goal + item order
    payload = {"main_item_id": MAIN, "item_order": ORDER}
    path = os.path.join(ROOT, "missions", "magic-squares", "proposal-meta.json")
    with io.open(path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=1)
    res = api("patch", "/mission-proposals/%s" % PROPOSAL, path)
    print("meta:", str(res)[:300])

    # 2. milestones
    for item_id, title, desc in MILESTONES:
        payload = {"item_id": item_id,
                   "milestone_title": title,
                   "milestone_description": desc}
        path = os.path.join(ROOT, "missions", "magic-squares", "milestone-tmp.json")
        with io.open(path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False, indent=1)
        res = api("post", "/mission-proposals/%s/milestones" % PROPOSAL, path)
        print("%-44s -> %s" % (title, res.get("id") or str(res)[:200]))


if __name__ == "__main__":
    main()
