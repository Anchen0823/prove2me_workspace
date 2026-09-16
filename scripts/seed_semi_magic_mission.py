# -*- coding: utf-8 -*-
"""Seed the semi-magic mission proposal: items, goal, order, milestones."""
import io, json, os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")
OUT = os.path.join(ROOT, "missions", "semi-magic")
PROPOSAL = "6ceb0b04-0e12-4909-a3b7-21581fe08d59"

REFS = [
    ("def MagicSquares", "be2f2b6a-a540-47ae-b487-ac22532a2745"),
    ("def MagicSquaresSemiMagic3", "983f535e-819e-4d18-baba-388fb3c39413"),
    ("def MagicSquaresCompositions", "73ed6522-7b76-4bfc-b852-f197b90ec3b2"),
    ("comps_card", "65af2905-cd30-4bb9-aa15-3ea5f86790e0"),
    ("sm3_canonical", "650b0511-bff1-4101-84b1-a49d5bef9849"),
    ("sm3_bij", "c4897555-460d-4fc5-8a01-732b5d8f39c9"),
    ("sm3_params_card", "7d09e267-c923-49c2-91f3-76185a464ad4"),
    ("semi_magic_count_three (GOAL)", "55e2191d-be25-4e6d-af7a-4635a34e5c63"),
]

MILESTONES = [
    ("650b0511-bff1-4101-84b1-a49d5bef9849",
     "Canonical decomposition into permutation matrices",
     "Every $3\\times3$ semi-magic square $M$ of line sum $t$ is a nonnegative integer "
     "combination $uD+vE+wF+xA+yB+zC$ of the six order-three permutation matrices, "
     "necessarily with $u+v+w+x+y+z=t$; and after normalizing by $\\min(x,y,z)=0$ the "
     "representation is **unique**. Existence is proved by subtracting the three even "
     "transversal minima and showing the residual has $M_{01}=M_{10}$ — a six-case "
     "linear-arithmetic argument — which is exactly the condition for the residual to be "
     "a combination of the three odd transversals alone."),
    ("65af2905-cd30-4bb9-aa15-3ea5f86790e0",
     "Stars and bars for compositions",
     "The number of compositions of $n$ into $k+1$ nonnegative parts is $\\binom{n+k}{n}$. "
     "Proved from scratch by splitting off the first coordinate (giving the recurrence "
     "$c(k+1,n)=\\sum_{i\\le n}c(k,n-i)$) together with the hockey-stick identity "
     "$\\sum_{j\\le n}\\binom{j+k}{j}=\\binom{n+k+1}{n}$. Needed here because the available "
     "library counts sub-multisets rather than compositions."),
    ("c4897555-460d-4fc5-8a01-732b5d8f39c9",
     "Bijection onto normalized parameters",
     "The map $(u,v,w,x,y,z)\\mapsto uD+vE+wF+xA+yB+zC$ is a bijection from the normalized "
     "coefficient vectors onto the $3\\times3$ semi-magic squares of line sum $t$, whence "
     "$H_{3}(t)=\\mathrm{sm3Count}(t)$. Requires a `Finset.card_bij` in both directions, "
     "coercing square entries into `Fin (t+1)` via the bound $M_{ij}\\le t$ and coefficient "
     "vectors into `Fin 6 → Fin (t+1)` via the sum condition."),
    ("7d09e267-c923-49c2-91f3-76185a464ad4",
     "Evaluating the parameter count",
     "Partitioning the normalized vectors by the *first* zero among $(x,y,z)$ writes "
     "$\\mathrm{sm3Count}(t)$ as $\\binom{t+4}{4}+\\binom{t+3}{4}+\\binom{t+2}{4}$, which "
     "two applications of Pascal's identity collapse to "
     "$3\\binom{t+3}{4}+\\binom{t+2}{2}$. This is the step where MacMahon's closed form "
     "actually appears; everything before it is a change of variables."),
    ("55e2191d-be25-4e6d-af7a-4635a34e5c63",
     "MacMahon's semi-magic count",
     "Assembling the two children: $H_{3}(t)=\\mathrm{sm3Count}(t)$ from the bijection, and "
     "$\\mathrm{sm3Count}(t)=3\\binom{t+3}{4}+\\binom{t+2}{2}$ from the parameter count. "
     "The result is a **polynomial** in $t$ of degree $4=(3-1)^{2}$, the order-three case of "
     "the Ehrhart/Stanley theorem that $H_{n}$ is a polynomial of degree $(n-1)^{2}$ — in "
     "contrast with the magic count $M_{3}$, which is only a quasi-polynomial."),
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
    item_ids = []
    for label, tid in REFS:
        payload = {"kind": "reference", "theorem_id": tid}
        path = os.path.join(OUT, "item-tmp.json")
        with io.open(path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False)
        res = api("post", "/mission-proposals/%s/items" % PROPOSAL, path)
        iid = res.get("id") or res.get("item_id")
        item_ids.append({"label": label, "theorem_id": tid, "item_id": iid})
        print("%-38s -> %s" % (label, iid or str(res)[:160]))
    with io.open(os.path.join(OUT, "proposal_items.json"), "w", encoding="utf-8") as fh:
        json.dump(item_ids, fh, ensure_ascii=False, indent=1)

    order = [r["item_id"] for r in item_ids if r["item_id"]]
    main_id = [r["item_id"] for r in item_ids
               if r["theorem_id"] == "55e2191d-be25-4e6d-af7a-4635a34e5c63"][0]
    payload = {"main_item_id": main_id, "item_order": order}
    path = os.path.join(OUT, "proposal-meta.json")
    with io.open(path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=1)
    print("meta:", str(api("patch", "/mission-proposals/%s" % PROPOSAL, path))[:200])

    tid2item = {r["theorem_id"]: r["item_id"] for r in item_ids}
    for tid, title, desc in MILESTONES:
        payload = {"item_id": tid2item[tid],
                   "milestone_title": title,
                   "milestone_description": desc}
        path = os.path.join(OUT, "milestone-tmp.json")
        with io.open(path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False, indent=1)
        res = api("post", "/mission-proposals/%s/milestones" % PROPOSAL, path)
        print("%-44s -> %s" % (title, res.get("id") or str(res)[:160]))


if __name__ == "__main__":
    main()
