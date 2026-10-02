"""Check exact types and axioms of the two integrated submission files offline."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
import workspace
OUT = ROOT / 'missions/kk-bin-packing/verification/volume-2026-10-02'

def main():
    lake, env = workspace.lake_environment()
    records = []
    for label, name, target_type in [
        ('lower', 'size_le_lin', 'SIZE I ≤ LIN I'),
        ('parent', 'size_le_lin_le_opt_le_lin_add',
         'SIZE I ≤ LIN I ∧ LIN I ≤ (OPT I : ℝ) ∧ (OPT I : ℝ) ≤ LIN I + ((numSizes I : ℝ) + 1) / 2'),
    ]:
        module = 'Solutions.Sol_KKBinPacking_GeometricGrouping_' + name
        source_path = module.replace('.', '/') + '.lean'
        source = (ROOT / source_path).read_text(encoding='utf-8')
        forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', source)
        assert not forbidden, (label, forbidden)
        assert 'import Theorems.Thm_KKBinPacking_GeometricGrouping_' + name + '\n' not in source
        audit_path = OUT / (label + '-type-axioms.lean')
        audit_path.write_text(
            'import ' + module + '\nopen KKBinPacking.Shared KKBinPacking.GeometricGrouping\n'
            'example (I : Multiset ℝ) (hI : IsInstance I) : ' + target_type + ' := solution I hI\n'
            '#print axioms solution\n' +
            ('#print axioms KKRoundingUpper.upper_from_sparse_approx_and_rounding\n' if label == 'parent' else ''),
            encoding='utf-8')
        run = subprocess.run([lake, 'env', 'lean', str(audit_path)], cwd=ROOT, env=env, capture_output=True)
        log = run.stdout.decode('utf-8', 'replace') + run.stderr.decode('utf-8', 'replace')
        (OUT / (label + '-type-axioms.log')).write_text(log, encoding='utf-8')
        if run.returncode or (label == 'lower' and 'sorryAx' in log):
            raise RuntimeError(label + ': ' + log)
        row = {'source': source_path, 'sha256': hashlib.sha256(source.encode()).hexdigest(),
               'exit_code': run.returncode, 'axiom_output': log,
               'imports': re.findall(r'^import (.+)$', source, re.M),
               'forbidden_tokens': forbidden,
               'classification': 'direct proof' if label == 'lower' else 'reduction with explicit theorem assumptions'}
        records.append(row)
        print(json.dumps(row, ensure_ascii=True), flush=True)
    (OUT / 'type-axiom-audit.json').write_text(json.dumps(records, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    check = subprocess.run([sys.executable, 'scripts/workspace.py', 'check'], cwd=ROOT, capture_output=True)
    check_log = check.stdout.decode('utf-8', 'replace') + check.stderr.decode('utf-8', 'replace')
    (OUT / 'workspace-check.txt').write_text(check_log, encoding='utf-8')
    print(json.dumps({'workspace_check_exit': check.returncode, 'details': check_log}), flush=True)

if __name__ == '__main__':
    main()
