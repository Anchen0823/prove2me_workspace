"""Wire the definition-free layer of the zeta(9) DAG into the private mission.

Publishes five new private theorem items (three provable abstract cores, two open
obligations), submits the three direct proofs, and submits two reductions of the
mission's goal theorem.  The concrete construction (coefficient matrices, Smith
data, weighted areas, congruence-lattice minima) is deliberately *not* invented
here: every published statement is either a general theorem about abstract data or
an obligation stated directly on zeta(9).  Mode --dump writes a snapshot of the
live milestone list before any write.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from submit_solved_milestones import post_multipart  # noqa: E402
from sync_private_proposal import RECEIPT, get_token, request  # noqa: E402


OUT = HERE / "wiring-receipt.json"
SNAPSHOT = HERE / "state-before.json"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"

NODES: dict[str, dict[str, Any]] = {
    "Z9.ONEFORM.CRITERION": {
        "name": "ZetaNine.irrational_of_small_nonzero_integer_forms",
        "title": "One-form irrationality criterion",
        "draft": "OneFormCriterion.lean",
        "statement": "OneFormCriterion-statement.md",
        "solution": "solutions/Sol_ZetaNine_irrational_of_small_nonzero_integer_forms.lean",
        "explanation": "solutions/OneFormCriterion-explanation.md",
        "milestone": ("TP2. One-form irrationality criterion",
                      "If for every epsilon>0 a real x admits a nonzero integer form "
                      "b+a*x with absolute value below epsilon, then x is irrational. "
                      "This is the formalised criterion half of local node TP: it turns a "
                      "supply of small nonzero integer forms in 1 and x into irrationality "
                      "of x, with no independence hypothesis. It is a proved general "
                      "statement about an arbitrary real number; the concrete zeta(9) "
                      "construction and the one-sign nonvanishing certificate remain part "
                      "of the open targets T, TG, TS and T5."),
        "source": "Local zeta9 research note, roadmap/research/full-lattice-sign-next.md and "
                  "roadmap/research/moving-short-sign-next.md, node TP, 2026-09-25",
    },
    "Z9.TP.SIGN": {
        "name": "ZetaNine.taylor_sign_implies_kernel_sum_pos",
        "title": "Positive Taylor sign forces a strictly positive kernel sum",
        "draft": "PositiveKernelSign.lean",
        "statement": "PositiveKernelSign-statement.md",
        "solution": "solutions/Sol_ZetaNine_taylor_sign_implies_kernel_sum_pos.lean",
        "explanation": "solutions/PositiveKernelSign-explanation.md",
        "milestone": ("TP1. Positive-kernel sign core",
                      "For a strictly positive kernel R, sampling map u and polynomial p, if "
                      "every sampling point satisfies u(k)>=u0, every Taylor coefficient of p "
                      "at u0 is nonnegative, the weighted series is summable and p is positive "
                      "at one sample, then the complete weighted sum is strictly positive. "
                      "This is the formalised positive-kernel half of local node TP: it rules "
                      "out a vanishing sum once a one-sign Taylor certificate is available. It "
                      "is stated for abstract data and does not assert that any concrete moving "
                      "first output of the zeta(9) construction carries such a sign."),
        "source": "Local zeta9 research note, roadmap/research/full-lattice-sign-next.md, "
                  "positive-kernel nonvanishing lemma, 2026-09-25",
    },
    "Z9.FQ.QUADRATURE": {
        "name": "ZetaNine.quadrature_exact_of_moments",
        "title": "Exact quadrature on quartics from the first five moments",
        "draft": "QuadratureMoments.lean",
        "statement": "QuadratureMoments-statement.md",
        "solution": "solutions/Sol_ZetaNine_quadrature_exact_of_moments.lean",
        "explanation": "solutions/QuadratureMoments-explanation.md",
        "milestone": ("FQ1. Exact quadrature from the first five moments",
                      "If a linear functional on the real polynomials and a five-node rule with "
                      "weights agree on the moments of degrees zero through four, then they "
                      "agree on every polynomial of degree at most four. This is the exact "
                      "algebraic core of local node FQ: it is the general moment-matching step "
                      "behind the five-sample cubature identity on the actual positive kernel. "
                      "It does not assert that the actual weights are strictly positive, which "
                      "is the analytic Gaussian-moment input, and it does not prove the open "
                      "infinite five-sample sign assertion T5."),
        "source": "Local zeta9 research note, roadmap/research/moving-short-sign-next.md, "
                  "section 6 exact five-sample cubature, 2026-09-25",
    },
    "Z9.OBLIG.ONE": {
        "name": "ZetaNine.exponentially_small_nonzero_forms_of_zeta_nine",
        "title": "Exponentially small nonzero integer forms in 1 and zeta(9)",
        "draft": "ExponentialOneFormObligation.lean",
        "statement": "ExponentialOneFormObligation-statement.md",
        "solution": None,
        "explanation": None,
        "milestone": ("R1. One-form route obligation",
                      "There is c>0 such that for all sufficiently large n some nonzero integer "
                      "form b+a*zeta(9) has absolute value below exp(-c*n). This is the open "
                      "analytic obligation of the one-form route and the child of the goal's "
                      "one-form reduction: the local notes derive it from the open lattice "
                      "margin J, the Gauss bound on the second minimum, the proved uniform "
                      "analytic decay, and the one-sign nonvanishing certificate. The statement "
                      "is strictly stronger than irrationality of zeta(9) and is not equivalent "
                      "to it."),
        "source": "Local zeta9 research note, roadmap/DAG.md section 'J to root' and "
                  "'Full lattice positive direction to root', 2026-09-25",
    },
    "Z9.OBLIG.TWO": {
        "name": "ZetaNine.exponentially_small_independent_forms_of_zeta_nine",
        "title": "Exponentially small independent integer forms in 1 and zeta(9)",
        "draft": "ExponentialTwoFormObligation.lean",
        "statement": "ExponentialTwoFormObligation-statement.md",
        "solution": None,
        "explanation": None,
        "milestone": ("R2. Two-form route obligation",
                      "There is c>0 such that for all sufficiently large n there are integers "
                      "with b1*a2 != b2*a1 and both |b_i+a_i*zeta(9)| below exp(-c*n). This is "
                      "the open analytic obligation of the mission's main two-form route and the "
                      "child of the goal's two-form reduction; it packages the open exponential "
                      "margin J, the coefficient map F, the analytic decay A and the Gauss bound "
                      "G. It is strictly stronger than the goal and is not equivalent to it."),
        "source": "Local zeta9 research note, roadmap/DAG.md section 'J to root' and "
                  "roadmap/research/arithmetic.md two-dimensional Gauss bound, 2026-09-25",
    },
}

REDUCTIONS: dict[str, dict[str, str]] = {
    "Z9.RED.ONEFORM": {
        "solution": "solutions/Sol_ZetaNine_irrational_zeta_nine_one_form.lean",
        "explanation": "solutions/IrrationalZetaNineOneForm-explanation.md",
        "children": "ZetaNine.irrational_of_small_nonzero_integer_forms, "
                    "ZetaNine.exponentially_small_nonzero_forms_of_zeta_nine",
    },
    "Z9.RED.TWOFORM": {
        "solution": "solutions/Sol_ZetaNine_irrational_zeta_nine_two_form.lean",
        "explanation": "solutions/IrrationalZetaNineTwoForm-explanation.md",
        "children": "ZetaNine.irrational_of_two_small_integer_forms, "
                    "ZetaNine.exponentially_small_independent_forms_of_zeta_nine",
    },
}

FINAL = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}


def saved() -> dict[str, Any]:
    if OUT.exists():
        data = json.loads(OUT.read_text(encoding="utf-8"))
        if data.get("schema") != "zeta9-dag-wiring-v1":
            raise ValueError("Unexpected wiring receipt schema")
        return data
    return {"schema": "zeta9-dag-wiring-v1", "results": {}, "milestones": {},
            "reductions": {}}


def save(data: dict[str, Any]) -> None:
    OUT.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def mission() -> dict[str, Any]:
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    if (receipt.get("status") != "Private" or receipt.get("visibility") != "private"
            or not receipt.get("mission_id")):
        raise RuntimeError("Expected the existing live private mission")
    return receipt


def body(item: dict[str, Any]) -> dict[str, Any]:
    code = (HERE / item["draft"]).read_text(encoding="utf-8")
    prefix, tail = code.split("namespace ZetaNine", 1)
    formal = ("namespace ZetaNine" + tail).strip()
    short_name = item["name"].split(".")[-1]
    if (formal.count(f"theorem {short_name}") != 1 or formal.count(":= by sorry") != 1
            or not formal.rstrip().endswith("end ZetaNine")):
        raise ValueError(f"Malformed theorem draft: {item['draft']}")
    return {
        "theorem_name": item["name"],
        "theorem_title": item["title"],
        "formal_statement": formal,
        "natural_language_statement":
            (HERE / item["statement"]).read_text(encoding="utf-8").strip(),
        "preamble": prefix.strip(),
        "source": item["source"],
        "tags": ["number-theory", "zeta-values", "irrationality"],
        "private": True,
        "env": ENV,
    }


def dump() -> None:
    receipt = mission()
    token = get_token()
    rows = request("GET", f"/missions/{receipt['mission_id']}/milestones?limit=200&offset=0",
                   token)
    SNAPSHOT.write_text(json.dumps(rows, ensure_ascii=False, indent=2) + "\n",
                        encoding="utf-8")
    print(f"Snapshot of {len(rows.get('milestones', []))} milestones -> {SNAPSHOT.name}")


def publish() -> None:
    mission()
    token = get_token()
    data = saved()
    for local_id, item in NODES.items():
        if data["results"].get(local_id, {}).get("job_id"):
            print(f"Already queued {local_id}")
            continue
        result = request("POST", "/submit-problem", token, body(item))
        jobs = result.get("jobs", [])
        if len(jobs) != 1 or jobs[0].get("name") != item["name"] or result.get("errors"):
            raise RuntimeError(f"Unexpected publish response for {local_id}: {result}")
        data["results"][local_id] = {"job_id": jobs[0]["job_id"], "name": item["name"],
                                     "job_status": "PENDING"}
        save(data)
        print(f"Queued private theorem {local_id}: {jobs[0]['job_id']}")


def poll_jobs() -> None:
    token = get_token()
    data = saved()
    for local_id, entry in data["results"].items():
        result = request("GET", f"/publish-jobs/{entry['job_id']}", token)
        if result.get("theorem_name") != entry["name"]:
            raise RuntimeError(f"Publish job mismatch: {local_id}")
        entry["job_status"] = result.get("status")
        entry["publish_error"] = result.get("error_message")
        if entry["job_status"] == "PUBLISHED":
            if result.get("visibility") != "private" or not result.get("theorem_id"):
                raise RuntimeError(f"Theorem was not published privately: {local_id}")
            entry["theorem_id"] = result["theorem_id"]
        elif entry["job_status"] in {"FAILED", "ERROR"}:
            raise RuntimeError(f"Publish failed for {local_id}: {entry['publish_error']}")
        print(f"{local_id} publish: {entry['job_status']}")
    save(data)


def prove() -> None:
    mission()
    token = get_token()
    data = saved()
    for local_id, item in NODES.items():
        if item["solution"] is None:
            continue
        entry = data["results"].get(local_id, {})
        if entry.get("submission_id"):
            print(f"Already submitted proof for {local_id}")
            continue
        if entry.get("job_status") != "PUBLISHED" or not entry.get("theorem_id"):
            raise RuntimeError(f"Theorem not yet published: {local_id}")
        theorem = request("GET", f"/theorems/{entry['theorem_id']}", token)
        if theorem.get("status") != "Open" or theorem.get("visibility") != "private":
            raise RuntimeError(f"Theorem not Open/private: {local_id}")
        path = HERE / item["solution"]
        source = path.read_text(encoding="utf-8")
        if "sorry" in source or source.count("theorem solution") != 1:
            raise RuntimeError(f"Solution has a placeholder: {local_id}")
        short_name = item["name"].split(".")[-1]
        target_sig = theorem["formal_statement"].split(f"theorem {short_name}", 1)[1] \
            .split(":= by sorry", 1)[0]
        local_sig = source.split("theorem solution", 1)[1].split(":= by", 1)[0]
        if target_sig != local_sig:
            raise RuntimeError(f"Solution signature differs from the live theorem: {local_id}")
        explanation = (HERE / item["explanation"]).read_text(encoding="utf-8")
        result = post_multipart(token, entry["theorem_id"], path, explanation)
        if not result.get("submission_id"):
            raise RuntimeError(f"No submission ID for {local_id}: {result}")
        entry["submission_id"] = result["submission_id"]
        entry["proof_status"] = result.get("status")
        entry["solution_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
        save(data)
        print(f"Submitted proof {local_id}: {entry['submission_id']}")


def squash(text: str) -> str:
    return " ".join(text.split())


def reduce() -> None:
    receipt = mission()
    token = get_token()
    data = saved()
    root_id = receipt["local_theorem_ids"]["Z9.R"]
    root = request("GET", f"/theorems/{root_id}", token)
    if root.get("status") != "Open" or root.get("visibility") != "private":
        raise RuntimeError("Goal theorem is no longer Open/private")
    expected = root["formal_statement"].split("theorem irrational_zeta_nine", 1)[1] \
        .split(":= by sorry", 1)[0]
    for local_id, item in REDUCTIONS.items():
        entry = data["reductions"].get(local_id, {})
        if entry.get("submission_id"):
            print(f"Already submitted reduction {local_id}")
            continue
        path = HERE / item["solution"]
        source = path.read_text(encoding="utf-8")
        if "sorry" in source or source.count("theorem solution") != 1:
            raise RuntimeError(f"Reduction contains a placeholder: {local_id}")
        local = source.split("theorem solution", 1)[1].split(":= by", 1)[0]
        if squash(local) != squash(expected):
            raise RuntimeError(f"Reduction type differs from the goal: {local_id}\n"
                               f"  goal: {squash(expected)!r}\n  local: {squash(local)!r}")
        for child in [c.strip() for c in item["children"].split(",")]:
            module = "Theorems.Thm_" + child.replace(".", "_")
            if f"import {module}" not in source:
                raise RuntimeError(f"Reduction {local_id} does not import child {module}")
        explanation = (HERE / item["explanation"]).read_text(encoding="utf-8")
        result = post_multipart(token, root_id, path, explanation)
        if not result.get("submission_id"):
            raise RuntimeError(f"No submission ID for {local_id}: {result}")
        entry.update({"theorem_id": root_id, "submission_id": result["submission_id"],
                      "status": result.get("status"), "children": item["children"],
                      "solution_sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        data["reductions"][local_id] = entry
        save(data)
        print(f"Submitted reduction {local_id}: {entry['submission_id']}")


def poll_proofs() -> None:
    token = get_token()
    data = saved()
    for local_id, entry in data["results"].items():
        if not entry.get("submission_id"):
            continue
        result = request("GET", f"/verify?submission_id={entry['submission_id']}", token)
        if result.get("theorem_id") != entry["theorem_id"]:
            raise RuntimeError(f"Proof target mismatch: {local_id}")
        entry["proof_status"] = result.get("status")
        entry["proof_error"] = result.get("error_message")
        print(f"{local_id} proof: {entry['proof_status']}")
    for local_id, entry in data["reductions"].items():
        result = request("GET", f"/verify?submission_id={entry['submission_id']}", token)
        entry["status"] = result.get("status")
        entry["error_message"] = result.get("error_message")
        print(f"{local_id} reduction: {entry['status']}")
    save(data)


def sync_mission() -> None:
    receipt = mission()
    token = get_token()
    data = saved()
    for local_id, item in NODES.items():
        entry = data["results"].get(local_id, {})
        if not entry.get("theorem_id"):
            raise RuntimeError(f"New theorem is not published: {local_id}")
        if item["solution"] and entry.get("proof_status") != "ACCEPTED":
            raise RuntimeError(f"New proved core is not accepted: {local_id}")
        theorem = request("GET", f"/theorems/{entry['theorem_id']}", token)
        if theorem.get("visibility") != "private":
            raise RuntimeError(f"New theorem is not private: {local_id}")
        want = "Proved" if item["solution"] else "Open"
        if theorem.get("status") != want:
            raise RuntimeError(f"New theorem status is {theorem.get('status')}, want {want}: {local_id}")

    current = request("GET", f"/missions/{receipt['mission_id']}/milestones?limit=200&offset=0",
                      token)
    existing = {row["title"]: row for row in current.get("milestones", [])}
    for local_id, item in NODES.items():
        title, description = item["milestone"]
        theorem_id = data["results"][local_id]["theorem_id"]
        if title in existing:
            row = existing[title]
            if (row.get("theorem") or {}).get("id") != theorem_id:
                raise RuntimeError(f"Existing milestone links a different theorem: {title}")
            if row.get("milestone_description") != description:
                row = request("PATCH", f"/milestones/{row['id']}", token, {
                    "milestone_description": description,
                    "reason": "Recorded the formalisable core of this local DAG node.",
                })
                if row.get("milestone_description") != description:
                    raise RuntimeError(f"Milestone update read-back failed: {title}")
                print(f"Updated milestone {title}")
            data["milestones"][local_id] = row["id"]
            save(data)
            continue
        row = request("POST", f"/missions/{receipt['mission_id']}/milestones", token, {
            "title": title, "milestone_description": description, "theorem_id": theorem_id})
        if row.get("title") != title or (row.get("theorem") or {}).get("id") != theorem_id:
            raise RuntimeError(f"Milestone read-back mismatch: {title}")
        data["milestones"][local_id] = row["id"]
        save(data)
        print(f"Added milestone {title} -> {theorem_id}")

    check = request("GET", f"/missions/{receipt['mission_id']}/milestones?limit=200&offset=0",
                    token)
    got = {row["title"]: row for row in check.get("milestones", [])}
    for local_id, item in NODES.items():
        title, description = item["milestone"]
        theorem_id = data["results"][local_id]["theorem_id"]
        row = got.get(title)
        if row is None or row.get("milestone_description") != description \
                or (row.get("theorem") or {}).get("id") != theorem_id:
            raise RuntimeError(f"Post-write milestone read-back failed: {title}")
    print(f"Verified {len(NODES)} new milestone links; "
          f"{len(check.get('milestones', []))} milestones total")


def main() -> None:
    parser = argparse.ArgumentParser()
    modes = parser.add_mutually_exclusive_group(required=True)
    for name in ("dump", "publish", "poll-jobs", "prove", "reduce", "poll-proofs",
                 "sync-mission"):
        modes.add_argument("--" + name, action="store_true")
    args = parser.parse_args()
    if args.dump:
        dump()
    elif args.publish:
        publish()
    elif args.poll_jobs:
        poll_jobs()
    elif args.prove:
        prove()
    elif args.reduce:
        reduce()
    elif args.poll_proofs:
        poll_proofs()
    else:
        sync_mission()


if __name__ == "__main__":
    main()
