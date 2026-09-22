"""Save exact source hashes and the platform verdict for the face/support proof."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MISSION = ROOT / 'missions/magic-squares-v'
SUB = MISSION / 'submissions'
payload = json.loads((SUB / 'real-cone-face-support-problem.json').read_text(encoding='utf-8'))
mirror = ROOT / 'Theorems/Thm_MagicSquares_real_cone_face_support_order_iso.lean'
mirror.write_text(payload['preamble'] + '\n\n' + payload['formal_statement'] + '\n', encoding='utf-8')
files = [f'examples/magic-squares/spencer/{name}.lean' for name in
         ('OrthantFaceOrder', 'SemiMagicCone', 'DoublyStochasticSupport', 'SemiMagicFaceSupport')]
files += ['Definitions/Def_MagicSquaresRealCone.lean',
          'Solutions/Sol_MagicSquares_real_cone_face_support_order_iso.lean']
verdict = json.loads((SUB / 'real-cone-face-support-verdict.json').read_text(encoding='utf-8-sig'))
record = {
    'lean': '4.33.1',
    'mathlib_rev': '0df444a360eaa60ab8c11dca51a86af692955474',
    'build': {'exit_code': 0, 'jobs': 8714, 'log': 'verification/semi-magic-face-build.log'},
    'axiom_audit': {'exit_code': 0, 'sorryAx': False,
                    'log': 'verification/semi-magic-face-axioms.log',
                    'standalone_log': 'verification/real-cone-face-support-compile.log'},
    'source_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in files},
    'submission': {k: verdict[k] for k in ('id', 'theorem_id', 'status', 'updated_at')},
    'remaining': 'General face-interval Euler relation and coefficient identification remain unproved; mission root is Open.'
}
(MISSION / 'verification/face-support-record.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
print(json.dumps(record['submission']))
