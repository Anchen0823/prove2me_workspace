"""Serialize new Mathlib-heavy imports, then run the required mission build."""
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
import workspace

OUT = ROOT / 'missions/kk-bin-packing/verification/volume-2026-10-02'
MODULES = [
    'Theorems.Thm_KKBinPacking_GeometricGrouping_opt_le_two_size_add_one',
    'Theorems.Thm_KKBinPacking_GeometricGrouping_size_le_lin',
    'Theorems.Thm_KKBinPacking_GeometricGrouping_exists_sparse_near_optimal_lp',
    'Theorems.Thm_KKBinPacking_GeometricGrouping_lp_floor_rounding_certificate',
]

def main():
    lake, env = workspace.lake_environment()
    evidence = []
    for module in MODULES:
        start = time.monotonic()
        run = subprocess.run([lake, 'build', module], cwd=ROOT, env=env, capture_output=True)
        log = run.stdout.decode('utf-8', 'replace') + run.stderr.decode('utf-8', 'replace')
        (OUT / (module.split('.')[-1] + '-build.log')).write_text(log, encoding='utf-8')
        row = {'module': module, 'exit_code': run.returncode, 'seconds': round(time.monotonic()-start, 2)}
        evidence.append(row)
        print(json.dumps(row), flush=True)
        if run.returncode:
            print(log.encode('ascii', 'backslashreplace').decode(), flush=True)
            raise SystemExit(run.returncode)
    run = subprocess.run([sys.executable, 'scripts/workspace.py', 'build', 'kk-bin-packing'],
                         cwd=ROOT, env=env, capture_output=True)
    log = run.stdout.decode('utf-8', 'replace') + run.stderr.decode('utf-8', 'replace')
    (OUT / 'mission-build.log').write_text(log, encoding='utf-8')
    evidence.append({'command': 'python scripts/workspace.py build kk-bin-packing', 'exit_code': run.returncode})
    (OUT / 'build-results.json').write_text(json.dumps(evidence, indent=2) + '\n', encoding='utf-8')
    print(log.encode('ascii', 'backslashreplace').decode(), flush=True)
    raise SystemExit(run.returncode)

if __name__ == '__main__':
    main()
