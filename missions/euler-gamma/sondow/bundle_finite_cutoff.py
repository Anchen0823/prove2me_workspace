"""Bundle locally checked proof modules into a self-contained Prove2Me submission."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[3]
visited = set()
imports = []
bodies = []
manifest = []

def visit(module):
    if module in visited:
        return
    visited.add(module)
    path = root / (module.replace('.', '/') + '.lean')
    content = path.read_text(encoding='utf-8-sig')
    body = []
    for line in content.splitlines():
        if line.startswith('import '):
            dependency = line.removeprefix('import ').strip()
            if dependency.startswith('Solutions.'):
                visit(dependency)
            elif dependency not in imports:
                imports.append(dependency)
        elif not line.startswith('#print axioms '):
            body.append(line)
    # Sections prevent module-local open declarations from leaking into other modules.
    bodies.append(f'-- Source: {module}\nsection\n' + '\n'.join(body).strip() + '\nend\n')
    manifest.append({'module': module, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})

visit('Solutions.SondowLogarithmicForms')
target = (root / 'Theorems/Thm_EulerMascheroni_Sondow_finite_cutoff_identity.lean').read_text(encoding='utf-8-sig')
target = target[target.index('theorem EulerMascheroni.Sondow.finite_cutoff_identity'):]
target = target.replace('theorem EulerMascheroni.Sondow.finite_cutoff_identity', 'theorem solution', 1)
target = target.replace(':= by sorry', ':= by\n  exact finite_cutoff_identity_of_logarithmic_forms_equal n N hn hN (signedLogForm_eq_L n)')
proof = '\n'.join('import ' + item for item in imports) + '\n\n'
proof += '\n'.join(bodies)
proof += '\nopen EulerMascheroni.Sondow\n\n' + target.strip() + '\n\n#print axioms solution\n'
destination = root / 'Solutions/Sol_EulerMascheroni_Sondow_finite_cutoff_identity.lean'
destination.write_text(proof, encoding='utf-8')
record = {'file': str(destination), 'sha256': hashlib.sha256(destination.read_bytes()).hexdigest(),
          'modules': manifest, 'imports': imports}
(root / 'missions/euler-gamma/sondow/continuation/finite-cutoff-bundle.json').write_text(
    json.dumps(record, indent=2), encoding='utf-8')
print(f'Bundled {len(manifest)} modules into {destination.name} ({len(proof.splitlines())} lines).')
