"""Record hashes and saved platform receipts without making network calls."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MISSION = ROOT / "missions/magic-squares-v"

def read(name):
    return json.loads((MISSION / "submissions" / name).read_text(encoding="utf-8-sig"))

definition = read("boundary-definition-job.json")
child = read("boundary-problem-job.json")
verdict = read("boundary-reciprocity-verdict.json")
paths = [
    "Definitions/Def_MagicSquaresMatchingBoundary.lean",
    "Theorems/Thm_MagicSquares_matching_boundary_euler.lean",
    "Solutions/Sol_MagicSquares_semi_magic_reciprocity_boundary.lean",
    "missions/magic-squares-v/scripts/assemble_boundary_reduction_bundle.py",
    "examples/magic-squares/spencer/MatchingBoundaryEasyCase.lean",
]
record = {
    "recorded_at": datetime.now(timezone.utc).isoformat(),
    "lean": "leanprover/lean4:v4.33.1",
    "mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474",
    "definition": {"id": definition["theorem_id"], "status": definition["status"]},
    "child": {"id": child["theorem_id"], "publish_status": child["status"], "proof_status": "Open"},
    "submission": {key: verdict.get(key) for key in ("id", "theorem_id", "status", "error_message", "updated_at")},
    "local_compilation": {"exit_code": 0, "log": "verification/boundary-bundle-compile.log"},
    "source_contains_sorry": False,
    "unproved_import": "MagicSquares.matching_boundary_euler",
    "full_mission_proved": False,
    "additional_local_result": "The branch permSupport sigma subset D is proved for arbitrary weights; opposite cancellation branch remains open.",
    "files": [{"path": p, "sha256": hashlib.sha256((ROOT / p).read_bytes()).hexdigest()} for p in paths],
}
out = MISSION / "verification/boundary-platform-record.json"
out.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"record": str(out), "status": verdict["status"]}))
