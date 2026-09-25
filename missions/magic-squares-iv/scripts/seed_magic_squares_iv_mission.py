# -*- coding: utf-8 -*-
"""Hang the Mission IV nodes off its proposal."""
import io, json, os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")
OUT = os.path.join(ROOT, "missions", "magic-squares-iv")
PROPOSAL = "7af96e14-bc8e-4e17-96b0-3aefec5f3a45"

GOAL = "0e66e443-931d-419d-8ec0-b925b0678288"

REFS = [
    ("def MagicSquaresSpecial3", "dc7c7ce9-2547-4cd2-9592-2974f777ff2a"),
    ("symmetric_magic_three_classify", "8ce82e6f-d4df-4db4-9a22-19e17c230371"),
    ("symm_three_bij", "0b52ef65-8a48-445f-a9bd-9a2c271ad6bb"),
    ("pan_three_card", "418897d2-7993-4acd-8625-687a351efb11"),
    ("pan_three_otherwise", "025bcf4a-7b1e-4813-acfa-27f69cf2dcd5"),
    ("symm_three_otherwise", "632cc340-833d-4a83-9537-d53be8c54378"),
    ("special_three_count (GOAL)", GOAL),
]

MILESTONES = [
    ("8ce82e6f-d4df-4db4-9a22-19e17c230371",
     "Symmetry is classified by a corner",
     "A symmetric $3\\times3$ magic square of line sum $3e$ is determined by its "
     "top-left corner $a=M_{00}$: it equals "
     "$\\begin{pmatrix}a&2e-a&e\\\\2e-a&e&a\\\\e&a&2e-a\\end{pmatrix}$. Symmetry "
     "identifies $M_{01}=M_{10}$, $M_{02}=M_{20}$, $M_{12}=M_{21}$, leaving five "
     "free cells and five line equations; the anti-diagonal $2M_{02}+M_{11}=3e$ "
     "forces $M_{02}=M_{11}=e$, and the rows then give "
     "$M_{01}=M_{10}=2e-a$, $M_{12}=M_{21}=a$, $M_{22}=2e-a$. This is the "
     "classification that the counting bijection is built on."),
    ("0b52ef65-8a48-445f-a9bd-9a2c271ad6bb",
     "The symmetric family is an interval",
     "Sending a symmetric magic square of order three and line sum $3e$ to its "
     "top-left corner is a bijection onto the admissible parameters "
     "$\\{0,1,\\dots,2e\\}$, so $S_{3}(3e)=2e+1$. Well-definedness is where "
     "truncated subtraction enters: the $(0,1)$ entry is $2e-a$, so the row "
     "identity $a+(2e-a)+e=3e$ is satisfiable in $\\mathbb{N}$ exactly when "
     "$a\\le 2e$. Surjectivity needs the two shape facts that "
     "$\\mathrm{symmMagic3}(e,a)$ is symmetric for every $a$ and is magic of line "
     "sum $3e$ for $a\\le 2e$."),
    ("418897d2-7993-4acd-8625-687a351efb11",
     "Panmagicity forces the constant square",
     "The only panmagic $3\\times3$ square of line sum $3e$ is the constant array "
     "with every entry $e$, so $P_{3}(3e)=1$. The twelve line equations (three "
     "rows, three columns, six broken diagonals) form a subtraction-free linear "
     "system over $\\mathbb{N}$ whose unique nonnegative solution is "
     "$a=b=\\dots=i=e$; the proof is a single `omega` call after the index "
     "arithmetic $i+k$ and $\\mathrm{rev}(i)+k$ on `Fin 3` is reduced. This is the "
     "degenerate counterpart of the symmetric family: imposing the six broken "
     "diagonals collapses the two-parameter MacMahon family to one point."),
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
        print("%-38s -> %s" % (label, iid or str(res)[:200]))
    with io.open(os.path.join(OUT, "proposal_items.json"), "w", encoding="utf-8") as fh:
        json.dump(item_ids, fh, ensure_ascii=False, indent=1)

    order = [r["item_id"] for r in item_ids if r["item_id"]]
    main_id = [r["item_id"] for r in item_ids if r["theorem_id"] == GOAL][0]
    payload = {"main_item_id": main_id, "item_order": order}
    path = os.path.join(OUT, "proposal-meta.json")
    with io.open(path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=1)
    print("meta:", str(api("patch", "/mission-proposals/%s" % PROPOSAL, path))[:250])

    tid2item = {r["theorem_id"]: r["item_id"] for r in item_ids}
    for tid, title, desc in MILESTONES:
        payload = {"item_id": tid2item[tid], "milestone_title": title,
                   "milestone_description": desc}
        path = os.path.join(OUT, "milestone-tmp.json")
        with io.open(path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False, indent=1)
        res = api("post", "/mission-proposals/%s/milestones" % PROPOSAL, path)
        print("%-45s -> %s" % (title, res.get("id") or str(res)[:180]))


if __name__ == "__main__":
    main()
