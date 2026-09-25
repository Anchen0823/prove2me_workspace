"""Rebuild the first-round report from archived exact evidence."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

BASE=Path(__file__).resolve().parents[1]
VERIFY=BASE/'verification'


def read(name):
    return json.loads((VERIFY/name).read_text(encoding='utf-8'))


def index(name):
    return [json.loads(line) for line in (VERIFY/name).read_text(encoding='utf-8').splitlines()]


def exact_endpoints(ball):
    scale=Fraction(10)**ball['exp']
    return (int(ball['mid'])-int(ball['rad']))*scale,(int(ball['mid'])+int(ball['rad']))*scale


def main():
    linear=index('linear-results.jsonl')
    gram=index('gram-results.jsonl')
    limits=read('arithmetic-improved-certificates.json')['limits']
    analytic=read('analytic-vertical-bound.json')['rows']
    independent=read('independent-audit.json')
    assert len(linear)==21 and len(gram)==23
    assert all(r['status']=='ok' and r['above_one'] for r in linear)
    ltable=[]
    for step in range(7):
        profile=[next(r for r in linear if r['n']==n and r['m']==step*n//28) for n in (56,112,224)]
        bounds=[tuple(x/r['n'] for x in exact_endpoints(r['abs_log_interval'])) for r in profile]
        assert all(lo>0 for lo,hi in bounds)
        assert bounds[1][0]>bounds[0][1]  # Exact intervals certify the failed promotion gate.
        label='0（控制）' if not step else str(Fraction(step,28))
        ltable.append('| '+label+' | '+' | '.join(f"{r['abs_log_per_n']:.6f}" for r in profile)+' |')
    promoted=[r for r in gram if r['s']==9 and r['K']==80]
    gtable=[]
    for r in sorted(promoted,key=lambda x:x['log_value_per_K2']):
        earlier=next(x for x in gram if x['case_id']==r['source_case_id'])
        gtable.append(f"| {r['q']} | {Fraction(r['N'],r['K'])} | {Fraction(r['h'],r['K'])} | "
                      f"{earlier['log_value_per_K2']:.6f} | {r['log_value_per_K2']:.6f} |")
    ctable=[]
    combined=[]
    for ar,an in zip(limits,analytic):
        assert ar['alpha']==an['alpha']
        cost=Fraction(ar['improved_cost_upper'])
        bound=cost+Fraction(an['H_global_strict_upper'])
        assert Fraction(ar['improved_cost_lower'])>0 and bound>0
        ceiling=-(-bound.numerator*10**6//bound.denominator)
        combined.append(dict(alpha=ar['alpha'],proved_combined_upper=str(bound),
                             interpretation='positive upper bound; no lower-bound or impossibility claim'))
        ctable.append(f"| {ar['alpha']} | {float(cost):.6f} | {an['H_global_strict_upper']} | {ceiling/10**6:.6f} |")
    summary=dict(date='2026-09-24',status='first_round_complete_no_irrationality_proof',
                 linear_samples=21,zeta9_gram_samples=21,regression_controls=2,
                 sample_failures_or_timeouts=0,linear_n448_promotions=0,
                 no_promotion_verified_by_exact_interval_endpoints=True,
                 all_zeta9_primitive_absolute_values_above_one=True,
                 proved_combined_upper_bounds=combined,
                 gcd_formula_audit=independent['gcd_formula'],
                 direct_tail_certificates=len(independent['linear_direct_sum']))
    assert all(r['direct_sum_excludes_zero'] for r in independent['linear_direct_sum'])
    (VERIFY/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    report=(BASE/'research/report-template.md').read_text(encoding='utf-8')
    report=report.replace('{{LINEAR}}','\n'.join(ltable)).replace('{{GRAM}}','\n'.join(gtable)).replace('{{COMBINED}}','\n'.join(ctable))
    (BASE/'report.md').write_text(report,encoding='utf-8')
    paths=sorted(p for p in BASE.rglob('*') if p.is_file() and '__pycache__' not in p.parts
                 and p.name!='artifact-manifest.json')
    manifest=[dict(path=p.relative_to(BASE).as_posix(),bytes=p.stat().st_size,
                   sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths]
    (VERIFY/'artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(files=len(manifest),samples=44,report=str(BASE/'report.md'))))


if __name__=='__main__':
    main()
