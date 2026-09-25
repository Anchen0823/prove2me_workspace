"""Gather the fourth-round exact certificates and verify immutable prior rounds."""
from __future__ import annotations
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'missions/zeta9/round4'
OUT=BASE/'verification'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(name):
    return json.loads((OUT/name).read_text(encoding='utf-8'))


def lower_interval(v):
    scale=Fraction(10)**v['exp']
    return (int(v['mid'])-int(v['rad']))*scale


def main():
    scan=read('prime-scan-summary.json')
    local=read('local-residue-audit.json')
    finite=read('obstruction-audit.json')
    highest=read('highest-audit.json')
    assert scan['status']=='ok' and scan['cases_done']==10
    assert scan['large_primes']==2428 and scan['nonzero']==2424
    assert local['status']=='passed' and local['exact_prime_comparisons']==200
    assert local['p_squared_boundary_rejected']
    exceptions=local['independently_lifted_exceptions']
    assert len(exceptions)==4 and all(e['certified_vp_B']==-8 for e in exceptions)
    assert finite['cases']==10 and finite['all_exact_rational_lower_bounds_gt_one']
    assert finite['n24_crosschecks']==2
    assert highest['status']=='ok' and highest['cases']==20
    rows=[]
    for entry in read('obstruction-index.json'):
        path=ROOT/entry['artifact']
        assert sha(path)==entry['sha256']
        data=json.loads(path.read_text(encoding='utf-8'))
        lower=lower_interval(data['primitive_log_lower_per_n'])
        rounded=(lower*100).__floor__()
        assert lower>Fraction(rounded,100)>0
        rows.append(dict(D=data['D'],n=data['n'],forced_outer_primes=data['forced_prime_count'],
                         available_outer_primes=data['prime_count'],
                         guaranteed_log_abs_primitive_per_n=f'{rounded//100}.{rounded%100:02d}',
                         artifact=str(path.relative_to(ROOT)),sha256=sha(path)))
    expected={(6,24):'35.43',(8,24):'50.89',(6,48):'31.19',(8,48):'51.33',
              (6,96):'35.00',(8,96):'51.81',(6,192):'34.32',(8,192):'52.65',
              (6,384):'34.70',(8,384):'52.57'}
    assert {(r['D'],r['n']):r['guaranteed_log_abs_primitive_per_n'] for r in rows}==expected
    previous=[]
    for directory in ('missions/zeta9','missions/zeta9/round2','missions/zeta9/round3'):
        base=ROOT/directory
        manifest=base/'verification/artifact-manifest.json'
        entries=json.loads(manifest.read_text(encoding='utf-8'))
        for entry in entries:
            path=base/entry['path']
            assert path.stat().st_size==entry['bytes'] and sha(path)==entry['sha256'],path
        previous.append(dict(directory=directory,files_verified=len(entries),
                             manifest_sha256=sha(manifest),unchanged=True))
    summary=dict(status='round_complete_no_irrationality_proof',date='2026-09-24',
                 universal_result='For all positive even n, sign(A_n,D)=(-1)^(n/2), so A_n,D is nonzero.',
                 proof_inputs=['Borcea-Branden arXiv math/0607416v6 Theorem 2(b)',
                               'Legendre simple zeros on (-1,1); exact Rodrigues identity'],
                 exact_coefficient_sanity_checks=20,
                 scan_parameters=10,prime_parameter_pairs=2428,
                 denominator_order_9=2424,denominator_order_8=4,
                 unresolved_scanned_pairs=0,exceptions=exceptions,
                 archived_prime_comparisons=200,comparison_moduli=['p','p^2'],
                 primitive_obstruction_certificates=rows,
                 conditional_obstruction='liminf (sum_good_outer_primes log(p))/n > 3 log(2) implies primitive exponential growth.',
                 unproved_condition='Uniform weighted density of primes with nonzero truncated residue sums.',
                 scope='Finite obstruction certificates plus a universal highest-coefficient lemma; neither an irrationality proof nor an unconditional impossibility theorem for the family.',
                 prior_artifacts=previous)
    (OUT/'summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    manifest_path=OUT/'artifact-manifest.json'
    # Create the target before validating local links; its final contents follow.
    if not manifest_path.exists():
        manifest_path.write_text('[]\n',encoding='utf-8')
    for path in BASE.rglob('*.md'):
        text=path.read_text(encoding='utf-8')
        assert not any(ord(c)<32 and c not in '\r\n\t' for c in text),path
        for target in re.findall(r'\]\(([^\s)]+)\)',text):
            if target.startswith(('http:','https:','#')):
                continue
            assert (path.parent/target.split('#')[0]).exists(),(path,target)
    manifest=[dict(path=str(path.relative_to(BASE)).replace('\\','/'),bytes=path.stat().st_size,sha256=sha(path))
              for path in sorted(BASE.rglob('*')) if path.is_file() and '__pycache__' not in path.parts
              and path!=manifest_path]
    manifest_path.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    for row in json.loads(manifest_path.read_text(encoding='utf-8')):
        assert sha(BASE/row['path'])==row['sha256']
    print(json.dumps(dict(status='ok',new_files_frozen=len(manifest),prime_pairs=2428,
                         order9=2424,order8=4,finite_certificates=10,
                         highest_checks=20,previous=previous),ensure_ascii=False))


if __name__=='__main__':
    main()
