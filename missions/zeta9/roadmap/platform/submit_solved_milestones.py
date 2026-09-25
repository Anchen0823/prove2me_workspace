"""Submit and read back the two locally compiled Lean proofs in the private mission.

Use --submit once, then --poll to refresh pending verdicts. Credentials are read
only in memory by sync_private_proposal; no token or API key is logged here.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import urllib.error
import urllib.request
import uuid
from pathlib import Path
from typing import Any

from sync_private_proposal import BASE, HERE, OPENER, RECEIPT, get_token, request


SUBMISSIONS = HERE / "solutions/proof-submissions.json"
TARGETS = {
    "Z9.P.FORMAL": (
        "ZetaNine.irrational_of_two_small_integer_forms",
        "Sol_ZetaNine_irrational_of_two_small_integer_forms.lean",
        "TwoFormsCriterion-explanation.md",
    ),
    "Z9.RED.J.FORMAL": (
        "ZetaNine.exponential_margin_of_volume_and_shape",
        "Sol_ZetaNine_exponential_margin_of_volume_and_shape.lean",
        "ExponentMarginBridge-explanation.md",
    ),
}
FINAL = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}


def state() -> dict[str, Any]:
    if not SUBMISSIONS.exists():
        return {"schema": "zeta9-private-proof-submissions-v1", "submissions": {}}
    result = json.loads(SUBMISSIONS.read_text(encoding="utf-8"))
    if result.get("schema") != "zeta9-private-proof-submissions-v1":
        raise ValueError("Unknown local submission receipt schema")
    return result


def save(data: dict[str, Any]) -> None:
    SUBMISSIONS.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n",
                           encoding="utf-8")


def assert_signature(local_id: str, theorem: dict[str, Any], source: str) -> None:
    expected_name = TARGETS[local_id][0]
    if (theorem.get("theorem_name") != expected_name or
            theorem.get("mathlib_rev") != "0df444a360eaa60ab8c11dca51a86af692955474" or
            theorem.get("visibility") != "private"):
        raise RuntimeError(f"Live theorem metadata mismatch: {local_id}")
    if "sorry" in source or re.search(r"import\s+Theorems\.Thm_", source):
        raise RuntimeError(f"Solution contains a placeholder or theorem import: {local_id}")
    statement = theorem["formal_statement"]
    short_name = expected_name.split(".")[-1]
    signature = statement.split(f"theorem {short_name}", 1)[1].split(":= by sorry", 1)[0]
    local_signature = source.split("theorem solution", 1)[1].split(":= by", 1)[0]
    if signature != local_signature or source.count("theorem solution") != 1:
        raise RuntimeError(f"Solution signature differs from the live theorem: {local_id}")


def post_multipart(token: str, theorem_id: str, path: Path,
                   explanation: str) -> dict[str, Any]:
    boundary = "codex-zeta9-" + uuid.uuid4().hex
    parts: list[bytes] = []

    def field(name: str, value: str) -> None:
        parts.append((f"--{boundary}\r\n"
                      f'Content-Disposition: form-data; name="{name}"\r\n\r\n'
                      f"{value}\r\n").encode("utf-8"))

    field("theorem_id", theorem_id)
    field("proof_type", "prove")
    field("explanation", explanation)
    parts.append((f"--{boundary}\r\n"
                  'Content-Disposition: form-data; name="file"; filename="solution.lean"\r\n'
                  "Content-Type: text/plain; charset=utf-8\r\n\r\n").encode("utf-8") +
                 path.read_bytes() + b"\r\n")
    parts.append(f"--{boundary}--\r\n".encode("utf-8"))
    req = urllib.request.Request(
        BASE + "/verify", data=b"".join(parts), method="POST",
        headers={"Authorization": "Bearer " + token,
                 "Accept": "application/json",
                 "Content-Type": f"multipart/form-data; boundary={boundary}"},
    )
    try:
        with OPENER.open(req, timeout=45) as response:
            return json.loads(response.read())
    except urllib.error.HTTPError as error:
        body = error.read(2000).decode("utf-8", "replace")
        raise RuntimeError(f"POST /verify: HTTP {error.code}: {body}") from None


def submit() -> None:
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    if receipt.get("status") != "Private" or receipt.get("visibility") != "private":
        raise RuntimeError("Mission is not confirmed private")
    token = get_token()
    data = state()
    for local_id, (name, filename, explanation_name) in TARGETS.items():
        if local_id in data["submissions"]:
            print(f"Already recorded {local_id}; run --poll")
            continue
        theorem_id = receipt["local_theorem_ids"][local_id]
        theorem = request("GET", f"/theorems/{theorem_id}", token)
        path = HERE / "solutions" / filename
        source = path.read_text(encoding="utf-8")
        assert_signature(local_id, theorem, source)
        if theorem.get("status") != "Open":
            raise RuntimeError(f"Target {name} is no longer Open")
        explanation = (HERE / "solutions" / explanation_name).read_text(encoding="utf-8")
        result = post_multipart(token, theorem_id, path, explanation)
        submission_id = result.get("submission_id")
        if not submission_id:
            raise RuntimeError(f"No submission ID returned for {local_id}: {result}")
        data["submissions"][local_id] = {
            "theorem_id": theorem_id,
            "submission_id": submission_id,
            "status": result.get("status"),
            "solution_path": f"solutions/{filename}",
            "solution_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "explanation_path": f"solutions/{explanation_name}",
        }
        save(data)
        print(f"Submitted {local_id}: {submission_id}; {result.get('status')}")


def poll() -> None:
    data = state()
    token = get_token()
    for local_id, entry in data["submissions"].items():
        result = request("GET", f"/verify?submission_id={entry['submission_id']}", token)
        if result.get("theorem_id") != entry["theorem_id"]:
            raise RuntimeError(f"Submission theorem mismatch: {local_id}")
        entry["status"] = result.get("status")
        entry["error_message"] = result.get("error_message")
        print(f"{local_id}: {entry['status']}")
        if entry["status"] not in FINAL | {"PENDING"}:
            raise RuntimeError(f"Unexpected verdict: {entry['status']}")
    save(data)


def main() -> None:
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--submit", action="store_true")
    group.add_argument("--poll", action="store_true")
    args = parser.parse_args()
    if args.submit:
        submit()
    else:
        poll()


if __name__ == "__main__":
    main()
