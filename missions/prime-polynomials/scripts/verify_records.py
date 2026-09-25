"""Independent trial-division checks of published witnesses; no 1 exception."""
import json
import math
from fractions import Fraction as F
from pathlib import Path

def value(co, x):
    return sum(a*x**i for i, a in enumerate(reversed(co)))

def trial(v):
    return v >= 2 and all(v % d for d in range(2, math.isqrt(v)+1))

root = Path(__file__).resolve().parents[1]/'verification'
for r in json.loads((root/'results.json').read_text()):
    for label, b in r['best'].items():
        co, length = b['coefficients_descending'], b['length']
        vals = [value(co, x) for x in range(length)]
        assert all(trial(v) for v in vals)
        nxt = value(co, length)
        if label == 'distinct_prefix':
            assert len(set(vals)) == length
            assert not trial(nxt) or nxt in vals
        else:
            assert not trial(nxt)

cases = [
 ('Ruby quadratic', [36,18,-1801], -33, 11, 45),
 ('2006 cubic', [-66,3845,-60897,251831], 0, 45, 46),
 ('DL integer quintic', [3,7,-340,-122,3876,997], -24,24,49),
 ('DL integer sextic', [1,2,-100,79,367,-3919,-4723], -18,25,44),
 ('DL rational quartic', [F(3,4),F(1,2),F(-4323,4),F(34415,2),-62099], -16,32,49),
 ('DL rational quintic', [F(1,4),F(1,2),F(-345,4),F(879,2),17500,70123], -27,29,57),
 ('DL rational sextic', [F(1,72),F(1,24),F(-1583,72),F(-3161,24),F(200807,36),F(97973,3),-11351], -45,12,58),
 ('Borghi 2026 quartic', [1,-106,3959,-60950,341227], 0,53,None),
]
out=[]
for name, co, lo, hi, distinct in cases:
    raw = [value(co,x) for x in range(lo,hi+1)]
    assert all(v.denominator==1 for v in raw)
    vals = [abs(int(v)) for v in raw]
    assert all(trial(v) for v in vals), name
    if distinct is not None:
        assert len(set(vals))==distinct, name
    boundaries = [int(value(co,lo-1)), int(value(co,hi+1))]
    assert all(not trial(abs(v)) for v in boundaries), name
    out.append(dict(name=name, coefficients_descending=list(map(str,co)),
                    interval=[lo,hi], length=len(vals), distinct=len(set(vals)),
                    all_positive=all(v>0 for v in raw),
                    max_abs_value=max(vals), boundary_values=boundaries))
print(json.dumps(out,indent=2))
(root/'verified_records.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
