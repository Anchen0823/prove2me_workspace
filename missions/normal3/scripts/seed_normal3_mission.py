# -*- coding: utf-8 -*-
"""Hang the classification nodes off the Mission III proposal."""
import io, json, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")
OUT = os.path.join(ROOT, "missions", "normal3")
PROPOSAL = "98d3dea7-dd0d-4f0c-abb0-96f8f845b808"

REFS = [
    ("def MagicSquaresParam3", "68eaae9b-d759-4a2a-83f6-741ecdbca5f8"),
    ("magic_three_normal_classify", "c677420b-bca2-41da-b9e3-f804919a1235"),
    ("magic_three_normal_eight (GOAL)", "15e75fbb-7830-416b-ac11-6471accdd4e9"),
]

MILESTONES = [
    ("c677420b-bca2-41da-b9e3-f804919a1235",
     "Normality inside the MacMahon family",
     "Characterize which admissible parameter pairs $(a,c)\\in\\mathrm{paramSet}\\ 5$ "
     "make $\\mathrm{mkMagic3}(5,a,c)$ normal: exactly the eight pairs "
     "$(2,4),(2,6),(4,2),(4,8),(6,2),(6,8),(8,4),(8,6)$. Normality first bounds "
     "$1\\le a,c\\le 9$, reducing the problem to $81$ ground instances; each is then "
     "decided by evaluation, after `IsNormal` is rewritten into explicit quantifiers "
     "over `Fin 3` and unfolded with `Fin.forall_fin_succ`."),
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
               if r["theorem_id"] == "15e75fbb-7830-416b-ac11-6471accdd4e9"][0]
    payload = {"main_item_id": main_id, "item_order": order}
    path = os.path.join(OUT, "proposal-meta.json")
    with io.open(path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=1)
    print("meta:", str(api("patch", "/mission-proposals/%s" % PROPOSAL, path))[:200])

    tid2item = {r["theorem_id"]: r["item_id"] for r in item_ids}
    for tid, title, desc in MILESTONES:
        payload = {"item_id": tid2item[tid], "milestone_title": title,
                   "milestone_description": desc}
        path = os.path.join(OUT, "milestone-tmp.json")
        with io.open(path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False, indent=1)
        res = api("post", "/mission-proposals/%s/milestones" % PROPOSAL, path)
        print("%-40s -> %s" % (title, res.get("id") or str(res)[:150]))


if __name__ == "__main__":
    main()
