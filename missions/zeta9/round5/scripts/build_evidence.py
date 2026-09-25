"""Assemble the final fifth-round evidence and freeze its reproducibility manifest."""
from __future__ import annotations
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from independent_round5 import ROOT, BASE, OUT, iv
from flint import arb, ctx, fmpq


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(name):
    return json.loads((OUT/name).read_text(encoding='utf-8'))


def bounds(v):
    unit = Fraction(10)**int(v['exp'])
    return (int(v['mid'])-int(v['rad']))*unit, (int(v['mid'])+int(v['rad']))*unit


def main():
    independent = read('independent-archives.json')
    arithmetic = read('arithmetic-audit.json')
    weighted = read('weighted-audit.json')
    height = read('independent-height-barrier.json')
    signs = read('independent-signs.json')
    assert independent['status'] == arithmetic['status'] == height['status'] == signs['status'] == 'passed'
    assert weighted['status'] == 'ok'
    last = {}
    for line in (OUT/'weighted-results.jsonl').read_text(encoding='utf-8').splitlines():
        row = json.loads(line)
        last[row['case_id']] = row
    maps = [{r['case_id']:r for r in group} for group in
            (independent['checks'], arithmetic['archives'], weighted['rows'])]
    data = {}
    total, small, pure, zero_records = 0, 0, 0, 0
    for path in sorted(OUT.glob('weighted-p*.json.gz')):
        with gzip.open(path, 'rt', encoding='utf-8') as stream:
            block = json.load(stream)
        case = block['case_id']
        digest = sha(path)
        assert digest == last[case]['artifact_sha256']
        assert digest == maps[0][case]['archive_sha256'] == maps[1][case]['source_sha256'] == maps[2][case]['artifact_sha256']
        assert maps[0][case]['direct']['direct_excludes_zero']
        assert block['source_sha256']['weighted_forms'] == sha(BASE/'scripts/weighted_forms.py')
        candidates = block['candidate_search']['selected']
        total += len(candidates)
        small += sum(c['arb']['below_one'] for c in candidates)
        pure += len(block['candidate_search']['constant_only_records'])
        zero_records += len(block['candidate_search']['zero_full_records'])
        data[case] = block
    assert len(data) == 17 and total == 94 and small == 9
    assert signs['cases'] == 58 and signs['elementary_half_line_sign_certificates'] == 55
    for row in height['checks']:
        assert row['source_sha256'] == sha(OUT/f"weighted-p9-n{row['n']}-m{row['n']}-R4.json.gz")
    assert arithmetic['height_barrier']['source_sha256'] == sha(OUT/'independent-height-barrier.json')
    assert arithmetic['script_sha256'] == sha(BASE/'scripts/certificate.py')

    profiles = []
    for p, div, R in ((9,1,4),(9,1,6),(9,1,8),(7,2,2),(7,2,3),(5,4,1),(5,4,2)):
        ns = []
        for n in (12,24):
            case = f'p{p}-n{n}-m{n//div}-R{R}'
            candidates = data[case]['candidate_search']['selected']
            idx = min(range(len(candidates)), key=lambda i:candidates[i]['arb']['abs_log_per_n'])
            chosen = candidates[idx]
            lo, hi = bounds(chosen['arb']['abs_log_interval'])
            lo, hi = lo/n, hi/n
            for c in candidates:
                a, b = bounds(c['arb']['abs_log_interval'])
                assert hi <= b/n
            ns.append(dict(n=n, case_id=case, selected_index=idx,
                           rn_display=chosen['arb']['abs_log_per_n'],
                           rn_lower=str(lo), rn_upper=str(hi),
                           below_one=bool(hi<0)))
        change_low = Fraction(ns[1]['rn_lower'])-Fraction(ns[0]['rn_upper'])
        assert change_low > 0
        eligible = ns[1]['below_one']
        profiles.append(dict(p=p, m_ratio=f'1/{div}', R=R, scales=ns,
                             rn_increase_strict=True, eligible_for_n48=eligible,
                             reason='n24 strict primitive value below one' if eligible else
                                    'no n24 small value, no rate improvement, and no p9 height <=1.30'))
    assert [(p['p'],p['R']) for p in profiles if p['eligible_for_n48']] == [(9,4)]
    extension = data['p9-n48-m48-R4']['candidate_search']['selected']
    assert all(bounds(c['arb']['abs_log_interval'])[0] > 0 for c in extension)

    # Human-readable full finite example, chosen only after the precommitted list.
    block = data['p9-n24-m24-R4']
    idx = next(i for i,c in enumerate(block['candidate_search']['selected']) if c['arb']['below_one'])
    c = block['candidate_search']['selected'][idx]
    example = dict(status='finite_nonzero_value_below_one_not_an_irrationality_proof',
                   case_id=block['case_id'], selected_index=idx, n=24, p=9, m=24, R=4,
                   source_archive_sha256=sha(OUT/'weighted-p9-n24-m24-R4.json.gz'),
                   W_coefficients=c['w'], raw_vector_B_A3_A5_A7_A9=c['raw_vector'],
                   primitive_coefficients_A9_B=c['normalized']['pair'],
                   primitive_multiplier=c['normalized']['multiplier'],
                   primitive_gcd=c['normalized']['content'],
                   W_sha256=c['W_sha256'], primitive_sha256=c['primitive_pair_sha256'],
                   Arb=c['arb'], positivity='All coefficients of W((n+1)(2n+1)+x) are positive.',
                   independent_original_product_sum=maps[0][block['case_id']]['direct'])
    (OUT/'best-finite-candidate.json').write_text(json.dumps(example,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

    # The backup cutoff uses a proved lower bound on the available upper-bound
    # expression, not a lower bound on the actual linear form.
    layers=[]
    for e in (1,2,4):
        for rho in (Fraction(1,3),Fraction(2,3)):
            for theta in (Fraction(1,2),Fraction(3,4),Fraction(1)):
                a=3*theta/(14+2*e*rho)
                b=rho*a
                assert 0<b<=a<Fraction(1,4) and 14*a+2*e*b<=3
                layers.append(dict(e=e,rho=str(rho),theta=str(theta),alpha2=str(a),alpha1=str(b),
                                   degree_condition=True,short_integerization_applicable=True,
                                   promoted=False))
    with ctx.workprec(256):
        assert arb(fmpq(5,4)).log().upper()<arb(fmpq(1,4)).lower()
        assert arb(4).log().upper()<arb(fmpq(3,2)).lower()
        x=arb(fmpq(3,22))
        stronger=11*((1+x)*(1+x).log()-x*x.log())
        assert stronger.upper()<arb(fmpq(459,100)).lower()
        backup=dict(status='stopped_by_rigorous_bound_limitation', profiles=layers,
                    rigorous_facts=['U > 0 from its y=0 value',
                                    'limsup log(G_n)/n < 8.25',
                                    'liminf log(d_n^9/G_n)/n > 0.75'],
                    coarse_upper_expression_lower_bound='0.75',
                    stronger_G_exponent_bound_interval=iv(stronger),
                    stronger_certificate_cost_lower_bound='4.41',
                    warning='Bounds concern this contour-majorant/integerization certificate; no lower bound on actual |L_n| or primitive size.')
    (OUT/'analytic-prescreen.json').write_text(json.dumps(backup,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    previous=[]
    for directory in ('missions/zeta9','missions/zeta9/round2','missions/zeta9/round3','missions/zeta9/round4'):
        base=ROOT/directory
        manifest=base/'verification/artifact-manifest.json'
        entries=json.loads(manifest.read_text(encoding='utf-8'))
        for entry in entries:
            path=base/entry['path']
            assert path.stat().st_size==entry['bytes'] and sha(path)==entry['sha256'],path
        previous.append(dict(directory=directory,files_verified=len(entries),
                             manifest_sha256=sha(manifest),unchanged=True))
    summary=dict(status='round_complete_no_irrationality_proof',date='2026-09-24',
                 new_pilot_blocks=14,regression_blocks=2,promotion_blocks=1,
                 completed_blocks=17,timeouts=0,unresolved_blocks=0,
                 selected_candidates=total,certified_nonzero=total,primitive_below_one=small,
                 pure_constant_enumeration_records=pure,zero_enumeration_records=zero_records,
                 stored_full_zero_rank_sum=sum(len(b['full_hnf']['basis']) for b in data.values()),
                 polynomial_identities=sum(r['polynomial_identities'] for r in independent['checks']),
                 local_pole_checks=sum(r['local_pole_checks'] for r in arithmetic['archives']),
                 direct_original_product_nonzero_checks=17,
                 half_line_sign_certificates=55,profiles=profiles,
                 n48_best_rn=min(c['arb']['abs_log_per_n'] for c in extension),
                 n96_run=False,n96_stop_reason='n48 all eight >1, worsening rate, no applicable uniform negative exponent proof',
                 backup_profiles=18,backup_promotions=0,
                 proved_uniform_results=['All-prime integerization including the constant coordinate.',
                   'p9 m=n full formal kernel classified by explicit telescopers.',
                   'For each fixed R>=4, integer reduction to degree 4 has polynomial overhead.'],
                 unproved_steps=['Uniform infinite family with controlled combined coefficient-height and primitive integerization cost.',
                   'Nonzero evaluated forms on an infinite subsequence.',
                   'Strictly negative combined exponent on that subsequence.'],
                 prior_artifacts=previous,formalization_started=False)
    (OUT/'summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    manifest_path=OUT/'artifact-manifest.json'
    if not manifest_path.exists():
        manifest_path.write_text('[]\n',encoding='utf-8')
    for path in BASE.rglob('*.md'):
        body=path.read_text(encoding='utf-8')
        assert not any(ord(c)<32 and c not in '\r\n\t' for c in body),path
        for target in re.findall(r'\]\(([^\s)]+)\)',body):
            if target.startswith(('http:','https:','#')):
                continue
            assert (path.parent/target.split('#')[0]).exists(),(path,target)
    manifest=[dict(path=str(path.relative_to(BASE)).replace('\\','/'),bytes=path.stat().st_size,sha256=sha(path))
              for path in sorted(BASE.rglob('*')) if path.is_file() and '__pycache__' not in path.parts and path!=manifest_path]
    manifest_path.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='passed',frozen_files=len(manifest),blocks=17,candidates=total,
                         below_one=small,polynomial_identities=summary['polynomial_identities'],
                         pure_constant_records=pure,prior_files=sum(r['files_verified'] for r in previous)),ensure_ascii=False))


if __name__=='__main__':
    main()
