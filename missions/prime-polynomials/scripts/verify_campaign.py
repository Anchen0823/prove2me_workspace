"""Independent integer-power evaluation and exact trial division of improvements."""
from pathlib import Path
import json
import argparse
from math import isqrt

ROOT=Path(__file__).resolve().parents[1]/'verification'
def value(co,x):
    return sum(a*x**i for i,a in enumerate(reversed(co)))
def factor(n):
    n=abs(n)
    if n<2:return n
    if n%2==0:return 2
    for d in range(3,isqrt(n)+1,2):
        if n%d==0:return d
    return n
def prime(n):return n>=2 and factor(n)==n
out=[]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--pattern',default='*.jsonl',help='Glob within verification directory')
args=parser.parse_args()
for path in sorted(ROOT.glob(args.pattern)):
    checked=[]
    unsupported=False
    for line in path.read_text().splitlines():
        if not line.strip():continue
        r=json.loads(line)
        required={'coefficients','lo','hi','length'}
        if not required.issubset(r) or r.get('denominator',1)!=1 or not all(type(c) is int for c in r['coefficients']):
            unsupported=True
            break
        co=r['coefficients']
        vals=[abs(value(co,x)) for x in range(r['lo'],r['hi']+1)]
        assert len(vals)==r['length']==len(set(vals)),r
        assert all(prime(v) for v in vals),r
        checked.append(r)
    if unsupported:
        out.append({'campaign':path.stem,'verification_status':'unsupported-schema',
                    'note':'Requires a separate verifier; NOT counted as verified.'})
        continue
    if not checked:
        out.append({'campaign':path.stem,'verified_improvements':0,'best':None,
                    'note':'Empty candidate log; this does not establish search completion.'})
        continue
    r=checked[-1]; co=r['coefficients']
    r['values']=[abs(value(co,x)) for x in range(r['lo'],r['hi']+1)]
    r['height']=max(map(abs,co))
    r['endpoints']=[{'x':x,'value':value(co,x),'abs_factor':factor(value(co,x))}
                    for x in [r['lo']-1,r['hi']+1]]
    out.append({'campaign':path.stem,'verified_improvements':len(checked),'best':r})
(ROOT/'campaign-verification.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out,indent=2))
