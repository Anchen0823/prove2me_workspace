"""Post-selection diagnostic of round6 candidates, using saved rigorous balls.

No candidate is generated or changed here. Rational interval arithmetic
extracts a common continued-fraction prefix and identifies exact matches.
"""
from __future__ import annotations
import gzip
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[4]
PREV = ROOT/'missions/zeta9/round6/verification'
OUT = ROOT/'missions/zeta9/round7/verification'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    if path.suffix == '.gz':
        with gzip.open(path,'rt',encoding='utf-8') as f:
            return json.load(f)
    return json.loads(path.read_text(encoding='utf-8'))


def endpoints(ball):
    unit=Q(10)**int(ball['exp'])
    return (int(ball['mid'])-int(ball['rad']))*unit,(int(ball['mid'])+int(ball['rad']))*unit


def saveq(x):
    return [str(x.numerator),str(x.denominator)]


def run():
    rows=[]; sources=[]; intervals=[]
    for n in [12,24,48,96,192]:
        path=PREV/f'independent-n{n}.json'
        record=read(path)
        search=read(PREV/f'search-n{n}.json.gz')
        assert record['search_sha256']==sha(PREV/f'search-n{n}.json.gz')
        sources.append(dict(path=path.relative_to(ROOT).as_posix(),sha256=sha(path)))
        for c in record['candidates']:
            B,A=map(int,c['primitive_pair_B_A'])
            low,high=endpoints(c['independent_value_interval'])
            assert A>0 and (low>0 or high<0)
            intervals.append(((low-B)/A,(high-B)/A))
            alo,ahi=(low,high) if low>0 else (-high,-low)
            product_lo,product_hi=A*alo,A*ahi
            rows.append(dict(n=n,selected_index=c['selected_index'],
                        B=str(B),A=str(A),error_times_denominator_interval=[saveq(product_lo),saveq(product_hi)],
                        certified_below_legendre_half=product_hi<Q(1,2),
                        best_in_frozen_shortlist=c['selected_index']==record['direct_best_selected_index'],
                        log_abs_per_n_display=search['selected'][c['selected_index']]['log_abs_per_n']))
    lo=max(x[0] for x in intervals);hi=min(x[1] for x in intervals)
    assert lo<hi
    initial=(lo,hi)
    a_list=[]; convergents=[]
    pm2,pm1,qm2,qm1=0,1,1,0
    while len(a_list)<10000:
        a,b=lo.numerator//lo.denominator,hi.numerator//hi.denominator
        if a!=b:
            break
        p=a*pm1+pm2;q=a*qm1+qm2
        a_list.append(a);convergents.append((p,q))
        pm2,pm1,qm2,qm1=pm1,p,qm1,q
        lo-=a;hi-=a
        if lo<=0:
            break
        lo,hi=1/hi,1/lo
    matches={pair:i for i,pair in enumerate(convergents)}
    best=[]
    for row in rows:
        key=(-int(row['B']),int(row['A']))
        row['common_prefix_convergent_index_zero_based']=matches.get(key)
        if row['certified_below_legendre_half']:
            assert key in matches, 'precision insufficient or CF disagreement'
        if row['best_in_frozen_shortlist']:
            best.append(dict(n=row['n'],convergent_index=matches.get(key),
                             product_upper_float=float(Q(*map(int,row['error_times_denominator_interval'][1]))),
                             A_digits=len(row['A'])))
    payload=dict(status='passed',diagnostic_only=True,
                 no_candidate_generation=True,input_sources=sources,
                 alpha_interval=[saveq(x) for x in initial],
                 common_partial_quotients=a_list,common_prefix_length=len(a_list),
                 common_convergent_matches=sum(row['common_prefix_convergent_index_zero_based'] is not None for row in rows),
                 best=best,candidates=rows,script_sha256=sha(Path(__file__)))
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'continued-fraction-audit.json').write_text(json.dumps(payload,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:payload[k] for k in ['status','common_prefix_length','common_convergent_matches','best']}),flush=True)


if __name__=='__main__':run()
