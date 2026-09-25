"""Independent exact trial division for rational quintic campaign witnesses."""
import json, math, hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[1]
pre=root/'verification/family_binomial_quintic_run'
def val(c,x):
    v=0
    for a in c: v=v*x+a
    assert v%4==0
    return v//4
def prime(n):
    if n<2:return False
    if n%2==0:return n==2
    return all(n%d for d in range(3,math.isqrt(n)+1,2))
rows=[]
for line in pre.with_suffix('.jsonl').read_text().splitlines():
    r=json.loads(line); c=r['coefficients']
    assert all(sum(a*x**(5-i) for i,a in enumerate(c))%4==0 for x in range(4))
    vals=[abs(val(c,x)) for x in range(r['lo'],r['hi']+1)]
    assert len(vals)==r['length']==len(set(vals))
    assert all(map(prime, vals))
    edges=[abs(val(c,x)) for x in (r['lo']-1,r['hi']+1)]
    assert all(not prime(v) or v in vals for v in edges)
    rows.append(dict(**r, values=vals,boundary_abs_values=edges,verified=True))
summary=json.loads(pre.with_suffix('.json').read_text())
assert 0 <= summary['completed_shapes'] <= summary['shapes']
if summary['termination_reason']=='finite_family_exhausted':
    R=summary['mutation_radius']
    expected=1+20*R+40*R*R
    assert summary['completed_shapes']==summary['shapes']==expected
source=root/'scripts/family_binomial_quintic.cpp'
out={'search':summary,'independent_trial_division':rows,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'rules':'Degree exactly five; integer-valued rational coefficients; absolute prime values pairwise distinct; input [-80,80].',
 'completed_shapes':summary['completed_shapes'],
 'scope':'Base numerator [1,2,-345,1758,70000,0]/4, add 210*t*binom(x,j) in one or two directions j in [1,5], t in [-30,30]; integer constant [-498960,508199]. Shapes sampled without repeat; timeout can interrupt a shape.',
 'sieve':'For odd p, values modulo p have period p. For p=2, period 8 is used. Any root with period T where 2*T<=58 rules out distinct length58. For remaining primes <=53, a root requires an output +/-p somewhere in the scanning range. Hence necessary filters preserve the target within the sampled family.',
 'limitations':'Best shorter runs are not exhaustive because the filter preserves only target length58. This is not a global optimum or an audited world-record search.'}
(root/'verification/family_binomial_quintic_verified.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps({'verified_witnesses':len(rows),'best_length':summary['best']['length'],'shapes':summary['shapes'],'scanned':summary['scanned_polynomials']}))
