"""Prepare the PUBLIC prove2.me proposal for "Equal Sums of Two Squares".

This prepares a Draft only. Nothing is submitted here: a human has to click
"Submit Proposal" in the web UI, after which the draft items are compiled into
immutable theorems and the proposal goes to moderation.

Modes:
  --check   offline validation of every draft file and read-back (no network)
  --fields  list available fields, to fill `field_ids` in proposal.json
  --sync    create/update the draft, its items, the goal, the order and milestones;
            verify everything by reading it back from the platform
  --status  read the proposal back from the platform
"""
from __future__ import annotations

import argparse
import json
import re
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent      # .../missions/two-squares/platform
WORKSPACE = HERE.parents[2]                 # parents: two-squares, missions, workspace
BASE = "https://prove2.me/api/v1"
EXPECTED_VERSION = "0.11.1"
SPEC = json.loads((HERE / "proposal.json").read_text(encoding="utf-8"))
RECEIPT = HERE / "proposal-receipt.json"


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
    credentials = json.loads((WORKSPACE / "credentials.json").read_text(encoding="utf-8"))
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


def draft_body(item: dict[str, Any]) -> dict[str, Any]:
    path = HERE / item["code_path"]
    code = path.read_text(encoding="utf-8")
    preamble, formal = code.split("\n", 1)
    if preamble != "import Mathlib" or formal.count(":= by sorry") != 1:
        raise ValueError(f"Unexpected Lean draft layout: {path.name}")
    if f"theorem {item['theorem_name'].split('.')[-1]}" not in formal:
        raise ValueError(f"Name does not match Lean draft: {path.name}")
    if re.search(r"(?m)^\s*sorry\b", formal.replace(":= by sorry", "")):
        raise ValueError(f"Extra sorry in draft: {path.name}")
    readback = (HERE / item["readback_path"]).read_text(encoding="utf-8").strip()
    if not re.search(r"(?m)^FAITHFUL$", readback):
        raise ValueError(f"Independent read-back is not FAITHFUL: {path.name}")
    return {
        "kind": item["kind"],
        "theorem_name": item["theorem_name"],
        "theorem_title": item["theorem_title"],
        "formal_statement": formal.strip(),
        "natural_language_statement": item["natural_language_statement"],
        "preamble": preamble,
        "source": item["source"],
        "tags": item["tags"],
        "readback": readback,
        "readback_model": "independent-agent",
    }


def check() -> None:
    """Offline validation of the spec and every draft file."""
    local_ids = [item["local_id"] for item in SPEC["draft_items"]]
    if len(local_ids) != len(set(local_ids)):
        raise RuntimeError("Duplicate local_id")
    if SPEC["main_local_id"] not in local_ids:
        raise RuntimeError("main_local_id is not one of the items")
    if sorted(SPEC["item_order"]) != sorted(local_ids):
        raise RuntimeError("item_order is not a permutation of the items")
    names = [item["theorem_name"] for item in SPEC["draft_items"]]
    if len(names) != len(set(names)):
        raise RuntimeError("Duplicate theorem_name")
    referenced = {Path(item["code_path"]).name for item in SPEC["draft_items"]}
    present = {p.name for p in (HERE / "statements" / "items").glob("*.lean")}
    if referenced != present:
        raise RuntimeError(f"items/ file set mismatch: extra {sorted(present - referenced)}, "
                           f"missing {sorted(referenced - present)}")
    milestone_items = {m["local_id"] for m in SPEC["milestones"]}
    if SPEC["main_local_id"] in milestone_items:
        raise RuntimeError("The goal carries no milestone")
    for item in SPEC["draft_items"]:
        body = draft_body(item)
        if body["natural_language_statement"] != item["natural_language_statement"]:
            raise RuntimeError("Natural language statement drifted")
        print(f"OK  {item['local_id']:10s} {item['theorem_name']}")
    print(f"{len(SPEC['draft_items'])} items, {len(SPEC['milestones'])} milestones, "
          f"goal = {SPEC['main_local_id']}")
    if not SPEC["field_ids"]:
        print("NOTE: field_ids is empty; run --fields first")


def save_receipt(proposal: dict[str, Any], item_ids: dict[str, str],
                 milestones: list[dict[str, Any]]) -> None:
    result = {
        "proposal_id": proposal.get("id"),
        "mission_id": proposal.get("mission_id"),
        "name": proposal.get("name"),
        "status": proposal.get("status"),
        "visibility": proposal.get("visibility"),
        "main_item_id": proposal.get("main_item_id"),
        "item_order": proposal.get("item_order"),
        "local_item_ids": item_ids,
        "local_theorem_ids": {
            local_id: next((item.get("theorem_id") for item in proposal.get("items", [])
                            if item.get("id") == item_id), None)
            for local_id, item_id in item_ids.items()
        },
        "milestones": [
            {"item_id": m.get("item_id"), "milestone_title": m.get("title")}
            for m in milestones
        ],
        "reviewed_docs_version": EXPECTED_VERSION,
        "submitted_by_human": proposal.get("status") != "Draft",
    }
    RECEIPT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n",
                       encoding="utf-8")


def detail(token: str, proposal_id: str) -> dict[str, Any]:
    return request("GET", f"/mission-proposals/{proposal_id}", token)


def sync() -> None:
    if not SPEC["field_ids"]:
        raise RuntimeError("field_ids is empty: run --fields and fill proposal.json first")
    token = get_token()
    listed = request("GET", "/mission-proposals?limit=100&offset=0", token)
    matches = [p for p in listed.get("proposals", []) if p.get("name") == SPEC["name"]]
    if len(matches) > 1:
        raise RuntimeError("More than one proposal has this exact name")
    if matches:
        proposal_id = matches[0]["id"]
        print(f"Reusing proposal {proposal_id}")
    else:
        proposal = request("POST", "/mission-proposals", token, {
            "name": SPEC["name"],
            "description": (HERE / SPEC["description_path"]).read_text(encoding="utf-8"),
            "mission_type": SPEC["mission_type"],
            "field_ids": SPEC["field_ids"],
            "visibility": SPEC["visibility"],
        })
        proposal_id = proposal["id"]
        print(f"Created {SPEC['visibility']} proposal draft {proposal_id}")

    proposal = detail(token, proposal_id)
    if proposal.get("status") != "Draft":
        raise RuntimeError(f"Proposal is no longer editable: {proposal.get('status')}")
    if proposal.get("visibility") != SPEC["visibility"]:
        raise RuntimeError(f"Proposal visibility is {proposal.get('visibility')}, "
                           f"expected {SPEC['visibility']}")

    item_ids: dict[str, str] = {}
    for item in SPEC["draft_items"]:
        wanted = draft_body(item)
        existing = proposal.get("items", [])
        found = next((x for x in existing
                      if x.get("theorem_name") == item["theorem_name"]), None)
        comparison_keys = [k for k in wanted if k != "kind"]
        if found is None or any(found.get(k) != wanted[k] for k in comparison_keys):
            found = request("POST", f"/mission-proposals/{proposal_id}/items", token, wanted)
            print(f"Synchronized draft {item['theorem_name']}")
        item_ids[item["local_id"]] = found["id"]

    desired_order = [item_ids[x] for x in SPEC["item_order"]]
    goal_id = item_ids[SPEC["main_local_id"]]
    description = (HERE / SPEC["description_path"]).read_text(encoding="utf-8")
    proposal = detail(token, proposal_id)
    if (proposal.get("main_item_id") != goal_id or
            proposal.get("item_order") != desired_order or
            proposal.get("description") != description or
            proposal.get("field_ids") != SPEC["field_ids"]):
        proposal = request("PATCH", f"/mission-proposals/{proposal_id}", token, {
            "main_item_id": goal_id,
            "item_order": desired_order,
            "description": description,
            "field_ids": SPEC["field_ids"],
        })
        print("Set the goal, item order, fields and description")

    current = request("GET", f"/mission-proposals/{proposal_id}/milestones", token)
    current_entries = current.get("milestones", [])
    for milestone in SPEC["milestones"]:
        item_id = item_ids[milestone["local_id"]]
        wanted = {"item_id": item_id,
                  "milestone_title": milestone["milestone_title"],
                  "milestone_description": milestone["milestone_description"]}
        found = next((m for m in current_entries if m.get("item_id") == item_id), None)
        if (found is None or found.get("title") != wanted["milestone_title"] or
                found.get("milestone_description") != wanted["milestone_description"]):
            request("POST", f"/mission-proposals/{proposal_id}/milestones", token, wanted)
            print(f"Synchronized milestone {milestone['milestone_title']}")

    proposal = detail(token, proposal_id)
    milestone_rows = request("GET", f"/mission-proposals/{proposal_id}/milestones",
                             token).get("milestones", [])
    remote_items = {item.get("id"): item for item in proposal.get("items", [])}
    for item in SPEC["draft_items"]:
        remote = remote_items.get(item_ids[item["local_id"]])
        wanted = draft_body(item)
        if remote is None or any(remote.get(key) != wanted[key] for key in wanted):
            raise RuntimeError(f"Draft item read-back mismatch: {item['theorem_name']}")
    expected_milestones = {
        (item_ids[m["local_id"]], m["milestone_title"], m["milestone_description"])
        for m in SPEC["milestones"]
    }
    actual_milestones = {
        (m.get("item_id"), m.get("title"), m.get("milestone_description"))
        for m in milestone_rows
    }
    if (proposal.get("status") != "Draft" or
            proposal.get("visibility") != SPEC["visibility"] or
            proposal.get("main_item_id") != goal_id or
            proposal.get("item_order") != desired_order or
            proposal.get("description") != description or
            actual_milestones != expected_milestones or
            len(proposal.get("items", [])) != len(item_ids)):
        raise RuntimeError("Read-back verification of the proposal failed")
    save_receipt(proposal, item_ids, milestone_rows)
    print(f"Verified {SPEC['visibility']} Draft: {proposal_id}; {len(item_ids)} items, "
          f"{len(milestone_rows)} milestones.")
    print("Nothing was submitted. A human must click 'Submit Proposal' in the web UI.")


def status() -> None:
    token = get_token()
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    proposal = detail(token, receipt["proposal_id"])
    milestones = request("GET", f"/mission-proposals/{receipt['proposal_id']}/milestones", token)
    save_receipt(proposal, receipt["local_item_ids"], milestones.get("milestones", []))
    fresh = json.loads(RECEIPT.read_text(encoding="utf-8"))
    print(f"status={proposal.get('status')} mission_id={proposal.get('mission_id')} "
          f"visibility={proposal.get('visibility')}")
    missing = [k for k, v in fresh.get("local_theorem_ids", {}).items() if not v]
    total = len(fresh.get("local_theorem_ids", {}))
    print(f"theorem_ids resolved: {total - len(missing)}/{total}")
    if missing:
        print("still without theorem_id:", ", ".join(sorted(missing)))


def fields() -> None:
    token = get_token()
    response = request("GET", "/fields?limit=200&offset=0", token)
    rows = response.get("fields", response if isinstance(response, list) else [])
    for row in rows:
        print(f"{row.get('id')}\t{row.get('name')}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--sync", action="store_true")
    parser.add_argument("--status", action="store_true")
    parser.add_argument("--fields", action="store_true")
    args = parser.parse_args()
    if args.check:
        check()
    elif args.fields:
        fields()
    elif args.status:
        status()
    elif args.sync:
        check()
        sync()
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
