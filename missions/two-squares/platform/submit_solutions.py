"""Submit the prepared proofs for the public proposal "Equal Sums of Two Squares".

The mission only accepts submissions after moderator approval, but the compiled theorems
exist as soon as the human clicks "Submit Proposal", so `--submit` works before approval
only with `--allow-pre-approval`.

Modes:
  --check    verify every local solution against its draft statement (no network writes)
  --submit   post each proof to its theorem (idempotent; records submission ids)
  --poll     read back the recorded submission statuses
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import time
import urllib.error
import urllib.request
import uuid
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent                  # .../missions/two-squares/platform
WORKSPACE = HERE.parents[2]                             # parents: two-squares, missions, workspace
BASE = "https://prove2.me/api/v1"
EXPECTED_VERSION = "0.11.1"
SPEC = json.loads((HERE / "proposal.json").read_text(encoding="utf-8"))
RECEIPT = HERE / "proposal-receipt.json"
SUBMISSIONS = HERE / "submissions-receipt.json"
PREFIX = "Sol_EqualTwoSquares_"
TERMINAL = {"ACCEPTED", "REJECTED", "WA", "SKETCH_WA", "TIMEOUT", "INTERNAL_ERROR"}


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request: Any, fp: Any, code: int, msg: str,
                         headers: Any, newurl: str) -> None:
        raise RuntimeError(f"Redirect refused: HTTP {code}")


OPENER = urllib.request.build_opener(NoRedirect)


def request(method: str, path: str, token: str | None = None,
            payload: dict[str, Any] | None = None) -> dict[str, Any]:
    if not path.startswith("/") or "://" in path or ".." in path:
        raise ValueError("Unsafe API path")
    headers = {"Accept": "application/json"}
    if token:
        headers["Authorization"] = "Bearer " + token
    data = None
    if payload is not None:
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(BASE + path, data=data, headers=headers, method=method)
    try:
        with OPENER.open(req, timeout=45) as response:
            raw = response.read()
            return json.loads(raw) if raw else {}
    except urllib.error.HTTPError as error:
        body = error.read(2000).decode("utf-8", "replace")
        raise RuntimeError(f"{method} {path}: HTTP {error.code}: {body}") from None


def get_token() -> str:
    credentials = json.loads((WORKSPACE / "credentials.json").read_text(encoding="utf-8-sig"))
    if (credentials.get("access_token") and
            credentials.get("expires_at", 0) > time.time() + 90):
        return credentials["access_token"]
    api_key = credentials.get("api_key")
    if not api_key:
        raise RuntimeError("No saved API key available")
    refreshed = request("POST", "/agent/refresh", payload={"api_key": api_key})
    if refreshed.get("version") != EXPECTED_VERSION:
        raise RuntimeError(f"Platform version {refreshed.get('version')!r} differs from the "
                           f"reviewed {EXPECTED_VERSION} docs; review the docs before syncing")
    token = refreshed.get("access_token")
    if not token:
        raise RuntimeError("Refresh returned no access token")
    return token


def squash(text: str) -> str:
    return " ".join(text.split())


def short_name(item: dict[str, Any]) -> str:
    return item["theorem_name"].split(".")[-1]


def solution_path(item: dict[str, Any]) -> Path:
    return HERE / "solutions" / f"{PREFIX}{short_name(item)}.lean"


def signature(short: str, source: str) -> str:
    return squash(source.split(f"theorem {short}", 1)[1].split(":= by", 1)[0])


def draft_signature(item: dict[str, Any]) -> str:
    return signature(short_name(item), (HERE / item["code_path"]).read_text(encoding="utf-8"))


def load() -> dict[str, Any]:
    if SUBMISSIONS.exists():
        return json.loads(SUBMISSIONS.read_text(encoding="utf-8"))
    return {"items": {}}


def save(data: dict[str, Any]) -> None:
    SUBMISSIONS.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n",
                           encoding="utf-8")


def check() -> None:
    """Validate every solution that exists locally; items without one are reported, not fatal.

    The proposal deliberately carries items that are not proved yet (the goal, the parity
    lemma, the factorisation lemma), so a missing file must not block submitting the rest.
    """
    ok = True
    for item in SPEC["draft_items"]:
        path = solution_path(item)
        explanation_path = HERE / "solutions" / f"{short_name(item)}-explanation.md"
        if not path.exists():
            print(f"[SKIP] {item['theorem_name']} -> no local solution yet")
            continue
        problems: list[str] = []
        if True:
            source = path.read_text(encoding="utf-8")
            if re.search(r"(?m)^\s*sorry\b", source):
                problems.append("solution contains a `sorry` placeholder")
            if source.count("theorem solution") != 1:
                problems.append("solution is not a single root-level `theorem solution`")
            elif signature("solution", source) != draft_signature(item):
                problems.append("solution signature differs from the draft statement")
            if "namespace" in source:
                problems.append("solution must not be wrapped in a namespace")
        if not explanation_path.exists():
            problems.append("explanation missing")
        elif len(explanation_path.read_text(encoding="utf-8").strip()) < 200:
            problems.append("explanation too short")
        print(f"[{'OK ' if not problems else 'BAD'}] {item['theorem_name']}"
              + ("" if not problems else " -> " + "; ".join(problems)))
        ok = ok and not problems
    ready = sum(1 for i in SPEC["draft_items"] if solution_path(i).exists())
    print(f"check passed: {ready}/{len(SPEC['draft_items'])} items ready"
          if ok else "check FAILED")
    if not ok:
        raise SystemExit(1)


def post_multipart(token: str, theorem_id: str, path: Path, explanation: str) -> dict[str, Any]:
    boundary = "codex-twosq-" + uuid.uuid4().hex
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
        with OPENER.open(req, timeout=60) as response:
            return json.loads(response.read())
    except urllib.error.HTTPError as error:
        body = error.read(2000).decode("utf-8", "replace")
        raise RuntimeError(f"POST /verify: HTTP {error.code}: {body}") from None


def submit(allow_pre_approval: bool = False, only: str | None = None) -> None:
    check()
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    if not receipt.get("mission_id") and not allow_pre_approval:
        raise RuntimeError("Mission is not live yet (mission_id is empty). Wait for moderator "
                           "approval and re-run --status, or pass --allow-pre-approval to post "
                           "onto the compiled theorems while the proposal is in review.")
    theorem_ids = receipt.get("local_theorem_ids", {})
    missing = [k for k, v in theorem_ids.items() if not v]
    if missing:
        raise RuntimeError(f"No theorem_id for {', '.join(sorted(missing))}; "
                           "run --status to refresh")
    token = get_token()
    data = load()
    for item in SPEC["draft_items"]:
        local_id = item["local_id"]
        if only and local_id != only:
            continue
        path = solution_path(item)
        if not path.exists():
            print(f"No local solution for {item['theorem_name']}; skipping")
            continue
        entry = data["items"].setdefault(local_id, {})
        if entry.get("submission_id"):
            print(f"Already submitted {item['theorem_name']}: {entry['submission_id']}")
            continue
        theorem_id = theorem_ids[local_id]
        theorem = request("GET", f"/theorems/{theorem_id}", token)
        if theorem.get("visibility") != "public":
            raise RuntimeError(f"Expected a public theorem: {item['theorem_name']}")
        if theorem.get("status") not in ("Open", None):
            print(f"Skipping {item['theorem_name']}: status={theorem.get('status')}")
            continue
        name = short_name(item)
        live = squash(theorem["formal_statement"].split(f"theorem {name}", 1)[1]
                      .split(":= by sorry", 1)[0])
        if live != signature("solution", path.read_text(encoding="utf-8")):
            raise RuntimeError(f"Live theorem differs from the local solution: "
                               f"{item['theorem_name']}")
        explanation = (HERE / "solutions" / f"{name}-explanation.md").read_text(
            encoding="utf-8")
        result = post_multipart(token, theorem_id, path, explanation)
        if not result.get("submission_id"):
            raise RuntimeError(f"No submission id for {item['theorem_name']}: {result}")
        entry["submission_id"] = result["submission_id"]
        entry["status"] = result.get("status")
        entry["theorem_id"] = theorem_id
        entry["solution_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
        save(data)
        print(f"Submitted {item['theorem_name']}: {entry['submission_id']}")
    save(data)
    print(f"{sum(1 for e in data['items'].values() if e.get('submission_id'))}"
          f"/{len(SPEC['draft_items'])} proofs submitted. Run --poll to track them.")


def poll() -> None:
    token = get_token()
    data = load()
    for local_id, entry in data["items"].items():
        if not entry.get("submission_id"):
            continue
        sub = request("GET", f"/submissions/{entry['submission_id']}", token)
        entry["status"] = sub.get("status")
        entry["verdict_source"] = "GET /submissions"
        print(f"{local_id}: {entry.get('status')}  {sub.get('result', '')}".rstrip())
    save(data)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--submit", action="store_true")
    parser.add_argument("--poll", action="store_true")
    parser.add_argument("--allow-pre-approval", action="store_true")
    parser.add_argument("--only", default=None, help="submit a single local id, e.g. ESQ.BF")
    args = parser.parse_args()
    if args.submit:
        submit(args.allow_pre_approval, args.only)
    elif args.poll:
        poll()
    elif args.check:
        check()
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
