"""Check only this round's exact types and direct-proof axioms."""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
from workspace import lake_environment

lake, env = lake_environment()
results = []
for name, source in [
    ('telescoping', HERE / 'TelescopingCheck.lean'),
    ('dominance', ROOT / 'Solutions/Sol_KKBinPacking_GeometricGrouping_geom_dominance_certificate.lean'),
    ('lp-monotone', ROOT / 'Solutions/Sol_KKBinPacking_GeometricGrouping_lin_mono_submultiset.lean'),
]:
    if name != 'telescoping':
        check = HERE / (name + '-Check.lean')
        check.write_text(source.read_text(encoding='utf-8') + '\n#print axioms solution\n', encoding='utf-8')
    else:
        check = source
    p = subprocess.run([lake, 'env', 'lean', str(check.relative_to(ROOT))], cwd=ROOT, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = p.stdout.decode('utf-8', 'replace')
    (HERE / (name + '-check.log')).write_text(output, encoding='utf-8')
    result = {'name': name, 'exit_code': p.returncode, 'output': output}
    results.append(result)
    print(json.dumps(result, ensure_ascii=True), flush=True)
    (HERE / 'local-checks.json').write_text(json.dumps(results, ensure_ascii=False, indent=2), encoding='utf-8')
    if p.returncode:
        raise SystemExit(p.returncode)
