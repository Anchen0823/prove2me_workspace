"""Verify all archived rational identities, summarize evidence, freeze hashes."""
from __future__ import annotations
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT/'missions/zeta9/round3'
OUT = BASE/'verification'
sys.path.insert(0, str(ROOT/'tmp/zeta7/exact_packages'))
sys.set_int_max_str_digits(0)
from flint import fmpq, fmpq_poly


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(name):
    return json.loads((OUT/name).read_text(encoding='utf-8'))


def q(v):
    return fmpq(int(v[0]), int(v[1]))


def identity(path):
    start = time.monotonic()
    data = json.loads(gzip.decompress(path.read_bytes()))
    D, n, m = (data[k] for k in ('D','n','m'))
    tail = path.name.startswith('tail-')
    t = fmpq_poly([0,1])
    numerator = fmpq_poly([q(data['F'])])
    denominator = fmpq_poly([1])
    if tail:
        shifts = list(range(-m,0))+list(range(n+1,n+m+1))
        assert q(data['F']) == fmpq(math.factorial(n)**9, math.factorial(m)**2)
        power = 9
    else:
        shifts = [fmpq(ell,D) for ell in range(-D*m,D*(n+m)+1)]
        assert q(data['F']) == fmpq(math.factorial(n)**(10-D), math.factorial(m)**(2*D))
        power = 10
    for ell in shifts:
        numerator *= t+ell
    for j in range(n+1):
        denominator *= (t+j)**power
    reconstructed = fmpq_poly([0])
    for j, cs in enumerate(data['pole_coefficients_j_by_s1_to9']):
        for s, cp in enumerate(cs,1):
            quotient, remainder = divmod(denominator,(t+j)**s)
            assert not remainder
            reconstructed += q(cp)*quotient
    assert numerator == reconstructed, path
    return dict(path=str(path.relative_to(BASE)), D=D,n=n,m=m,
                family='tail' if tail else 'dense',
                numerator_degree=numerator.degree(), denominator_degree=denominator.degree(),
                full_polynomial_identity=True, sha256=sha(path),
                seconds=time.monotonic()-start)


def verify_prior():
    result = []
    for base in (ROOT/'missions/zeta9',ROOT/'missions/zeta9/round2'):
        manifest = base/'verification/artifact-manifest.json'
        entries = json.loads(manifest.read_text(encoding='utf-8'))
        for item in entries:
            path = base/item['path']
            assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], path
        result.append(dict(manifest=str(manifest.relative_to(ROOT)),
                           manifest_sha256=sha(manifest), files_verified=len(entries),unchanged=True))
    return result


def main():
    paths = sorted(OUT.glob('shift-D*.json.gz'))+sorted(OUT.glob('tail-shift-D*.json.gz'))
    assert len(paths) == 31
    identities = [identity(path) for path in paths]
    (OUT/'full-polynomial-audit.json').write_text(json.dumps(dict(status='ok',records=31,
        method='exact equality of full numerator and cleared partial-fraction polynomial',
        rows=identities,script_sha256=sha(Path(__file__))),indent=2)+'\n',encoding='utf-8')
    dense, tail = read('shift-audit.json'), read('tail-shift-audit.json')
    arithmetic = read('arithmetic-audit.json')
    direct, direct_tail = read('independent-audit.json'), read('tail-independent-audit.json')
    assert dense['status']==tail['status']==direct['status']==direct_tail['status']=='ok'
    assert arithmetic['status']=='passed'
    assert dense['records']==25 and dense['all_primitive_above_one']
    assert tail['records']==tail['primitive_above_one']==6
    assert arithmetic['atom_count']==25 and arithmetic['tail_count']==6
    assert direct['cases']==5 and direct_tail['cases']==3
    prior = verify_prior()
    summary = dict(status='round_complete_no_irrationality_proof',date='2026-09-24',
        exact_cases=31,dense_cases=25,tail_cases=6,
        primitive_abs_above_one=31,raw_abs_below_one=10,
        full_archived_polynomial_identities=31,independent_direct_sum_cases=8,
        direct_sum_bits=[640,1024],arithmetic_certificate_cases=31,
        arithmetic_small_parameter_checks=arithmetic['self_test'],
        larger_scale_promotions=0,prior_artifacts=prior,
        dense=dense['rows'],tail=tail['rows'],
        remaining_obstacle='No sufficiently cheap integerization yields a proved negative net exponent; no universal primitive lower bound either.',
        proof_scope='Single-zeta support, finite all-prime certificates, and the conditional-parameter raw real asymptotics in the notes. No Lean formalization or external peer review.')
    (OUT/'summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    # Reject accidental control characters in mathematical Markdown.
    for path in BASE.rglob('*.md'):
        text = path.read_text(encoding='utf-8')
        assert not any(ord(c)<32 and c not in '\r\n\t' for c in text), path
    manifest_path=OUT/'artifact-manifest.json'
    manifest = [dict(path=str(path.relative_to(BASE)).replace('\\','/'),
                     bytes=path.stat().st_size,sha256=sha(path))
                for path in sorted(BASE.rglob('*')) if path.is_file()
                and '__pycache__' not in path.parts and path!=manifest_path]
    manifest_path.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    for item in json.loads(manifest_path.read_text(encoding='utf-8')):
        assert sha(BASE/item['path'])==item['sha256']
    print(json.dumps(dict(status='ok',archived_identities=31,direct_cases=8,
                          arithmetic_cases=31,files_frozen=len(manifest),prior=prior),ensure_ascii=False))


if __name__=='__main__':
    main()
