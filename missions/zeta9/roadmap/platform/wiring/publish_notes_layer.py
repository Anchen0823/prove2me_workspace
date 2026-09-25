"""Publish the next layer of note-proved zeta(9) nodes to the private mission.

Four nodes, all of them definition-free: the five-sample non-vanishing certificate
(a reduction onto the already accepted quadrature core), the positive-weight
sandwich, the weighted-mediant interval (a reduction onto the sandwich) and the
positive-cone step of the Taylor transfer.  Modes mirror publish_wiring.py; every
write is read back.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
from publish_wiring import mission, squash  # noqa: E402
from submit_solved_milestones import post_multipart  # noqa: E402
from sync_private_proposal import get_token, request  # noqa: E402


OUT = HERE / "notes-layer-receipt.json"
SNAPSHOT = HERE / "notes-layer-state-before.json"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"

NODES: dict[str, dict[str, Any]] = {
    "Z9.NV.FIVESAMPLE": {
        "name": "ZetaNine.five_sample_sign_forces_nonzero",
        "title": "Five-sample one-sign test forces non-vanishing",
        "draft": "FiveSampleNonvanishing.lean",
        "statement": "FiveSampleNonvanishing-statement.md",
        "solution": "solutions/Sol_ZetaNine_five_sample_sign_forces_nonzero.lean",
        "explanation": "solutions/FiveSampleNonvanishing-explanation.md",
        "children": ["ZetaNine.quadrature_exact_of_moments"],
        "milestone": (
            "TP3. Five-sample nonvanishing certificate",
            "For a real linear functional L on R[X], five distinct nodes y, five strictly "
            "positive weights w and moment agreement L(X^m)=sum_j w_j y_j^m for 0<=m<=4, "
            "every nonzero polynomial of degree at most four whose five sampled values are "
            "weakly of one sign satisfies L(p)!=0. This is the exact composition of local "
            "nodes FQ and TP: FQ supplies the cubature identity, the root count excludes a "
            "vanishing quartic, and positivity of the weights converts weak sign into strict "
            "non-vanishing. It does not assert that the actual weights are positive (that is "
            "the Gaussian-moment input GC) nor that any actual moving output passes the test "
            "(open target T5)."),
        "source": "Local zeta9 research note, roadmap/research/moving-short-sign-next.md "
                  "sections 5-6 and roadmap/DAG.md node TP, 2026-09-25",
    },
    "Z9.FI.SANDWICH": {
        "name": "ZetaNine.min_lt_weighted_average_lt_max",
        "title": "Positive weights sandwich their weighted average",
        "draft": "PositiveWeightSandwich.lean",
        "statement": "PositiveWeightSandwich-statement.md",
        "solution": "solutions/Sol_ZetaNine_min_lt_weighted_average_lt_max.lean",
        "explanation": "solutions/PositiveWeightSandwich-explanation.md",
        "children": [],
        "milestone": (
            "FI1. Positive-weight sandwich",
            "If w_j>0, sum_j w_j=1 and the vector r is not constant, then the weighted "
            "average S=sum_j w_j r_j is strictly above some sampled value and strictly below "
            "another. This is the ordering heart of local node FI; the non-constancy "
            "hypothesis is the abstract counterpart of the rank-two non-degeneracy of the "
            "inverse image. The lemma says nothing about the width of the interval, the "
            "exponential contraction rate, or whether the moving first output avoids it."),
        "source": "Local zeta9 research note, roadmap/research/five-point-ratio-window.md, "
                  "strict five-sample ratio window, 2026-09-25",
    },
    "Z9.FI.MEDIANT": {
        "name": "ZetaNine.mediant_strictly_between_min_and_max",
        "title": "Weighted ratio interval contains the ratio of the sums",
        "draft": "RatioInterval.lean",
        "statement": "RatioInterval-statement.md",
        "solution": "solutions/Sol_ZetaNine_mediant_strictly_between_min_and_max.lean",
        "explanation": "solutions/RatioInterval-explanation.md",
        "children": ["ZetaNine.min_lt_weighted_average_lt_max"],
        "milestone": (
            "FI2. Weighted-mediant ratio interval",
            "With w_j>0, b_j>0 and not all ratios a_j/b_j equal, the mediant "
            "(sum_j w_j a_j)/(sum_j w_j b_j) lies strictly between the smallest and the "
            "largest sampled ratio. This is local node FI in its invariant (normalisation-"
            "free) form and is the reformulation that turns the open five-sample sign target "
            "T5 into a statement about the rational slope of the changing first output. No "
            "width or separation is asserted."),
        "source": "Local zeta9 research note, roadmap/research/five-point-ratio-window.md, "
                  "and roadmap/DAG.md section 'Five-sample first direction to root', 2026-09-25",
    },
    "Z9.TA.CONE": {
        "name": "ZetaNine.positive_matrix_maps_nonneg_to_pos",
        "title": "Entrywise positive matrix maps the nonnegative cone into the positive cone",
        "draft": "PositiveCone.lean",
        "statement": "PositiveCone-statement.md",
        "solution": "solutions/Sol_ZetaNine_positive_matrix_maps_nonneg_to_pos.lean",
        "explanation": "solutions/PositiveCone-explanation.md",
        "children": [],
        "milestone": (
            "TA1. Positive-cone step of the Taylor transfer",
            "For a real 5x5 matrix M with all entries strictly positive and a nonzero vector "
            "v>=0 entrywise, every coordinate of Mv is strictly positive. This isolates the "
            "cone step of local node TA: the note's one-step Taylor transfer has mixed signs "
            "and fails to preserve the cone, while the two-step transfer H_n H_(n+2) is "
            "eventually strictly positive and the same lemma applied to that product gives "
            "the two-step statement. It does not formalise the limit matrix, the eventual "
            "positivity of the actual two-step transfer, or the -10.1109 width rate."),
        "source": "Local zeta9 research note, roadmap/research/taylor-connection-next.md and "
                  "roadmap/research/taylor-window-rate.md, 2026-09-25",
    },
}

FINAL = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}


def saved() -> dict[str, Any]:
    if OUT.exists():
        data = json.loads(OUT.read_text(encoding="utf-8"))
        if data.get("schema") != "zeta9-notes-layer-v1":
            raise ValueError("Unexpected notes-layer receipt schema")
        return data
    return {"schema": "zeta9-notes-layer-v1", "results": {}, "milestones": {}}


def save(data: dict[str, Any]) -> None:
    OUT.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


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
        if entry.get("submission_id") and entry.get("proof_status") in {
                "ACCEPTED", "SKETCH_ACCEPTED", "PENDING"}:
            print(f"Already submitted proof for {local_id}")
            continue
        if entry.get("submission_id"):
            # A previous attempt was rejected; keep it in the history and retry.
            entry.setdefault("history", []).append(
                {"submission_id": entry["submission_id"], "status": entry.get("proof_status"),
                 "error_message": entry.get("proof_error"),
                 "solution_sha256": entry.get("solution_sha256")})
            for key in ("submission_id", "proof_status", "proof_error", "solution_sha256"):
                entry.pop(key, None)
            save(data)
            print(f"Retrying {local_id} after {entry['history'][-1]['status']}")
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
        if squash(target_sig) != squash(local_sig):
            raise RuntimeError(f"Solution signature differs from the live theorem: {local_id}")
        for child in item["children"]:
            module = "Theorems.Thm_" + child.replace(".", "_")
            if f"import {module}" not in source:
                raise RuntimeError(f"{local_id} does not import child {module}")
        explanation = (HERE / item["explanation"]).read_text(encoding="utf-8")
        result = post_multipart(token, entry["theorem_id"], path, explanation)
        if not result.get("submission_id"):
            raise RuntimeError(f"No submission ID for {local_id}: {result}")
        entry["submission_id"] = result["submission_id"]
        entry["proof_status"] = result.get("status")
        entry["solution_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
        save(data)
        print(f"Submitted proof {local_id}: {entry['submission_id']}")


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
    save(data)


def sync_mission() -> None:
    receipt = mission()
    token = get_token()
    data = saved()
    for local_id, item in NODES.items():
        entry = data["results"].get(local_id, {})
        if entry.get("proof_status") not in {"ACCEPTED", "SKETCH_ACCEPTED"}:
            raise RuntimeError(f"New node is not accepted: {local_id} "
                               f"({entry.get('proof_status')})")
        theorem = request("GET", f"/theorems/{entry['theorem_id']}", token)
        if theorem.get("status") not in {"Proved", "Open"} or theorem.get("visibility") != "private":
            raise RuntimeError(f"New theorem state unexpected: {local_id}")
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
    for name in ("dump", "publish", "poll-jobs", "prove", "poll-proofs", "sync-mission"):
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
    elif args.poll_proofs:
        poll_proofs()
    else:
        sync_mission()


if __name__ == "__main__":
    main()
