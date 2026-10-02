"""Assemble locally checked proof components into the standalone submission file."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = ROOT / 'missions/kk-bin-packing'
REL = 'Solutions/Sol_KKBinPacking_GeometricGrouping_alg2_step3_card_le.lean'

header = '''-- Karmarkar--Karp, Algorithm 2: packing and bin count after Step 3.
-- Source: FOCS 1982, pp. 315--317.
-- The helpers below are proved from platform definitions and Mathlib only.
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2

set_option autoImplicit false

'''
parts = []
for name in ['Grouping', 'Packing', 'Count']:
    text = (HERE / 'research' / (name + '.lean')).read_text(encoding='utf-8')
    parts.append('\n'.join(line for line in text.splitlines() if not line.startswith('import ')).strip())

target = json.loads((HERE / 'verification/target-before.json').read_text(encoding='utf-8'))
statement = target['formal_statement']
statement = statement.replace('namespace KKBinPacking.GeometricGrouping\n', '')
statement = statement.replace('end KKBinPacking.GeometricGrouping', '')
statement = statement.replace('theorem alg2_step3_card_le', 'theorem solution')
statement = statement.replace(':= by sorry', ''' := by
  exact ⟨KKContribution.step3_packing k g I hI tr
    (KKContribution.geom_partition k) (KKContribution.geom_pair_le k),
    KKContribution.step3_card_bound k g I tr⟩''')
source = header + '\n\n'.join(parts) + '\n\n' + statement.strip() + '\n'
for forbidden in ['sorry', 'axiom ', 'unsafe ', 'native_decide', 'import Theorems.', 'import Solutions.']:
    if forbidden in source:
        raise RuntimeError('Forbidden submission content: ' + forbidden)
(ROOT / REL).write_bytes(source.encode('utf-8'))
scope_path = HERE / 'scope.json'
scope = json.loads(scope_path.read_text(encoding='utf-8'))
scope['build'] = [REL]
scope['sources'] = sorted(set(scope['sources'] + [REL]))
scope['note'] = 'One formal submission root; Lake builds its actual definition dependencies. Research components are in research/.'
scope_path.write_bytes((json.dumps(scope, indent=2) + '\n').encode('utf-8'))
print(REL)
