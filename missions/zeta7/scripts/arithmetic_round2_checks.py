"""Reproduce structural finite certificates; optionally combine Newton bounds.

Does not compute determinants or modify the shared experiment artifacts.
All multiplier comparisons use Fraction. Reported logarithms are not intervals.
"""
from __future__ import annotations

from fractions import Fraction
import json
import math
from pathlib import Path
import time

from arithmetic_finite_certificate import certificate, compare_primitive


BASE = Path(__file__).resolve().parents[1]
VERIFY = BASE / 'verification'


def scale_log(K, layers, h, g):
    """log S_fact; matches round2_energy.py, including finite factors of 4."""
    return (2*h*math.lgamma(K+1)+(h-1)*math.log(4)
            -4*h*sum(q*math.lgamma(n+1) for n,q in layers)
            -2*sum(math.lgamma(2*(g+i)+1) for i in range(h)))


def combine_newton(cert, newton):
    byp={row['p']:row['lower_bound'] for row in newton['local']}
    numerator=denominator=1
    rows=[]
    for row in cert['prime_bounds']:
        p=row['p']
        lower=max(row['gamma'],byp.get(p,row['gamma']))
        if lower<0: numerator*=p**(-lower)
        else: denominator*=p**lower
        rows.append(dict(p=p,structural=row['gamma'],
                         newton=byp.get(p),combined=lower))
    result=dict(cert)
    ratio=Fraction(numerator,denominator)
    result['multiplier_numerator']=str(ratio.numerator)
    result['multiplier_denominator']=str(ratio.denominator)
    result['log_multiplier_per_K2']=(math.log(ratio.numerator)-math.log(ratio.denominator))/cert['K']**2
    result['combined_prime_bounds']=rows
    result['newton_source']='verification/round2-newton-certificates.json'
    return result


def audit_existing(exact):
    """Check all applicable pre-existing exact records, without new determinants."""
    checks=[]
    skipped=[]
    for case,row in exact.items():
        if row['s']!=7:
            skipped.append(dict(case_id=case,reason='s is not 7'))
            continue
        exponents=row['exponents']
        h=len(exponents)
        g=exponents[0]
        if exponents!=list(range(g,g+h)):
            skipped.append(dict(case_id=case,reason='exponents are not one shifted block'))
            continue
        zero={int(j):q for j,q in row['zero_multiplicities'].items()}
        nmax=max(zero,default=0)
        layers=[]
        for n in range(1,nmax+1):
            diff=zero.get(n,0)-zero.get(n+1,0)
            if diff<0: raise AssertionError('Existing record is not a prefix-layer profile')
            if diff: layers.append((n,diff))
        c=certificate(row['K'],layers,h,g)
        comparison=compare_primitive(c,row)
        checks.append(dict(case_id=case,K=row['K'],h=h,g=g,
                           gap_log_per_K2=comparison['log_ratio_per_K2'],
                           ratio_is_positive_integer=comparison['ratio_is_positive_integer']))
    artifact=dict(kind='comparison_with_pre_existing_exact_records',
                  checked_count=len(checks),skipped=skipped,checks=checks,
                  boundary='A consistency check of formulas, not a substitute for their proof.')
    (VERIFY/'arithmetic_round2_existing_audit.json').write_text(json.dumps(artifact,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(existing_records_checked=len(checks),skipped=len(skipped))),flush=True)


def main():
    exact={}
    for line in (VERIFY/'round2-results.jsonl').read_text(encoding='utf-8').splitlines():
        row=json.loads(line)
        if 'primitive_scale_numerator' in row: exact[row['case_id']]=row
    newton={r['case_id']:r for r in json.loads((VERIFY/'round2-newton-certificates.json').read_text())}
    finite=[]
    for K in (40,80):
        for shift40 in (0,1,2):
            route='A' if shift40==0 else 'B'
            case=f'K{K}-{route}-s7-n3q1_n6q3-h20-g{shift40}'
            layers=[(3*K//40,1),(6*K//40,3)]
            h,g=K//2,shift40*K//40
            c=certificate(K,layers,h,g)
            c['case_id']=case
            c['primitive_comparison']=compare_primitive(c,exact[case])
            sl=scale_log(K,layers,h,g)
            c['log_normalized_multiplier_per_K2']=c['log_multiplier_per_K2']-sl/K**2
            if case in newton:
                combined=combine_newton(c,newton[case])
                c['with_newton']=dict(
                    multiplier_numerator=combined['multiplier_numerator'],
                    multiplier_denominator=combined['multiplier_denominator'],
                    prime_bounds=combined['combined_prime_bounds'],
                    primitive_comparison=compare_primitive(combined,exact[case]),
                    log_normalized_multiplier_per_K2=combined['log_multiplier_per_K2']-sl/K**2)
            finite.append(c)
            print(json.dumps(dict(case_id=case,
                                  structural_gap=c['primitive_comparison']['log_ratio_per_K2'],
                                  combined_gap=c.get('with_newton',{}).get('primitive_comparison',{}).get('log_ratio_per_K2'),
                                  normalized_cost=c['log_normalized_multiplier_per_K2'])),flush=True)
    (VERIFY/'arithmetic_round2_finite_certificates.json').write_text(json.dumps(finite,indent=2)+'\n',encoding='utf-8')
    larger=[]
    for K in (160,320):
        for shift40 in (0,1):
            start=time.monotonic()
            layers=[(3*K//40,1),(6*K//40,3)]
            h,g=K//2,shift40*K//40
            c=certificate(K,layers,h,g)
            c['log_normalized_multiplier_per_K2']=c['log_multiplier_per_K2']-scale_log(K,layers,h,g)/K**2
            c['comparison_boundary']='No exact Delta evaluation or primitive scale at this K; comparison with U_sampled is heuristic.'
            c['elapsed_seconds']=time.monotonic()-start
            larger.append(c)
            print(json.dumps(dict(K=K,g=g,normalized_cost=c['log_normalized_multiplier_per_K2'],seconds=c['elapsed_seconds'])),flush=True)
    (VERIFY/'arithmetic_round2_largerK_certificates.json').write_text(json.dumps(larger,indent=2)+'\n',encoding='utf-8')
    audit_existing(exact)


if __name__=='__main__': main()
