"""Replace the generated flat cover search with a balanced explicit case tree.

The original integer certificates and endpoint proofs are retained verbatim.
Lean, not this transformation, checks the resulting proof.
"""
import re
from pathlib import Path

path = Path('Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_psi_bound.lean')
source = path.read_text(encoding='utf-8')
start = source.index('  have hcover :')
end = source.index('\nend TaoFivePrimes', start)
old = source[start:end]
cover = old.splitlines()[0]
intervals = [(int(a), int(b)) for a, b in re.findall(r'\((\d+) ≤ n ∧ n ≤ (\d+)\)', cover)]
bodies = re.split(r'^  · ', old, flags=re.M)[1:]
assert len(intervals) == len(bodies) == 87

def tree(lo, hi, indent):
    pad = ' ' * indent
    if hi - lo == 1:
        a, b = intervals[lo]
        body = bodies[lo].rstrip().splitlines()
        lines = [pad + f'have h : {a} ≤ n ∧ n ≤ {b} := by omega']
        lines += [pad + body[0]]
        lines += [pad + line[4:] if line.startswith('    ') else line for line in body[1:]]
        return lines
    mid = (lo + hi) // 2
    bound = intervals[mid-1][1]
    lines = [pad + f'by_cases hsplit_{bound} : n ≤ {bound}']
    for left, right in [(lo, mid), (mid, hi)]:
        child = tree(left, right, indent + 2)
        lines.append(pad + '· ' + child[0].lstrip())
        lines.extend(child[1:])
    return lines

source = source[:start] + '\n'.join(tree(0, len(intervals), 2)) + '\n' + source[end:]
path.write_text(source, encoding='utf-8')
print('Replaced the 87-way cover search with a balanced case tree.')
