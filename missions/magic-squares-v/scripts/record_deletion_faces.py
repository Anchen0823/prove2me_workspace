"""Record source hashes and terminal platform receipts for this increment."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
MISSION = ROOT / "missions/magic-squares-v"
sources = [
    "examples/magic-squares/spencer/" + name + ".lean"
    for name in ("MatchingDeletion", "SupportIntervalIE", "OrthantFace",
                 "OrthantFaceSupport", "OrthantCoordinateFace")
] + ["Solutions/Sol_Finset_interval_inclusion_exclusion.lean",
     "Solutions/Sol_Orthant_coordinate_face.lean"]
proofs = []
for stem in ("interval-inclusion-exclusion", "orthant-coordinate-face"):
    path = MISSION / "submissions" / (stem + "-verdict.json")
    if path.exists():
        receipt = json.loads(path.read_text(encoding="utf-8-sig"))
        proofs.append({k: receipt[k] for k in
                       ("id", "theorem_id", "status", "updated_at")})
record = {
    "lean": "4.33.1",
    "mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474",
    "local_build": {"exit_code": 0, "jobs": 8743,
                    "log": "verification/deletion-face-build.log"},
    "axioms": {"exit_code": 0, "sorryAx": False,
               "log": "verification/deletion-face-axioms.log"},
    "sources": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
                for p in sources},
    "platform_proofs": proofs,
    "remaining": "General matching-covered interval Euler relation is unproved; mission root remains Open.",
}
out = MISSION / "verification/deletion-face-record.json"
out.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
print(out.relative_to(ROOT))
