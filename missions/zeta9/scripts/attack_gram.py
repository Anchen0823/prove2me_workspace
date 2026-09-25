"""Bounded, resumable zeta(9) Gram controls; finite evidence only."""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
OLD = ROOT / 'missions/zeta7/scripts'
sys.path.insert(0, str(OLD))
from exact_hankel import parameters, evaluate, record, moment

BASE = ROOT / 'missions/zeta9/verification'
INDEX = BASE / 'gram-results.jsonl'
SCRIPT = Path(__file__).resolve()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def make_case(K, n40, q, h40, s=9, source=None):
    assert K % 40 == 0
    return dict(case_id=f's{s}-K{K}-N{n40*K//40}-q{q}-h{h40*K//40}',
                s=s, K=K, N=n40*K//40, q=q, h=h40*K//40,
                n40=n40, h40=h40, source_case_id=source)


def worker(case):
    start = time.monotonic()
    result = parameters(case['s'], case['K'], case['N'], case['q'], case['h'])
    full = record(result, evaluate(result), True)
    full.update(case)
    full.update(status='ok', seconds=time.monotonic()-start,
                runtime=dict(python=sys.version, exact_sha256=sha(OLD/'exact_hankel.py'),
                             runner_sha256=sha(SCRIPT)))
    target = BASE/'gram-coeff'/(case['case_id']+'.json.gz')
    target.parent.mkdir(parents=True, exist_ok=True)
    tmp = target.with_name(target.name+f'.{os.getpid()}.tmp')
    with gzip.open(tmp, 'wt', encoding='utf-8') as f:
        json.dump(full, f, separators=(',', ':'))
    tmp.replace(target)
    out = {k:v for k,v in full.items() if k not in ('primitive_coefficients_ascending',
           'denominator', 'numerator_content', 'primitive_scale_numerator', 'primitive_scale_denominator')}
    out.update(artifact_path=target.relative_to(ROOT).as_posix(), artifact_sha256=sha(target))
    return out


def run_one(case):
    start=time.monotonic()
    try:
        p=subprocess.run([sys.executable, str(SCRIPT), '--worker', json.dumps(case)],
                         cwd=ROOT, capture_output=True, text=True, encoding='utf-8', timeout=120)
        if p.returncode:
            raise RuntimeError((p.stderr or p.stdout)[-1500:])
        return json.loads(p.stdout)
    except Exception as exc:
        return dict(**case,status='unresolved',error=f'{type(exc).__name__}: {exc}',
                    seconds=time.monotonic()-start)


def load_known():
    return {r['case_id']:r for r in map(json.loads, INDEX.read_text(encoding='utf-8').splitlines())} if INDEX.exists() else {}


def run_stage(cases, known, workers, remaining):
    pending=[c for c in cases if known.get(c['case_id'],{}).get('status')!='ok'][:remaining[0]]
    with ThreadPoolExecutor(max_workers=workers) as pool:
        for f in as_completed([pool.submit(run_one,c) for c in pending]):
            row=f.result()
            with INDEX.open('a',encoding='utf-8') as dest:
                dest.write(json.dumps(row,separators=(',',':'))+'\n')
                dest.flush(); os.fsync(dest.fileno())
            known[row['case_id']]=row
            remaining[0]-=1
            print(row['case_id'],row['status'],row.get('log_value_per_K2'),flush=True)
    return [known[c['case_id']] for c in cases if known.get(c['case_id'],{}).get('status')=='ok']


def self_test():
    a=parameters(9,8,1,2,4)
    b=parameters(9,8,1,2,4,exponents=[0,1,2,3])
    assert a['coeffs']==b['coeffs']
    for x in (-1,0,1,3):
        assert a['delta'](x)==(a['A']+x*a['B']).det()
    assert moment(9,0)==3*moment(3,0)
    for p in (11,13,17):
        assert all(int(moment(9,e).denom())%p for e in range(4*p-5))
        assert int(moment(9,4*p-5).denom())%p==0
    return dict(default_explicit_basis_equal=True,direct_determinants=4,
                moment_threshold_primes=[11,13,17])


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--worker')
    p.add_argument('--workers',type=int,default=2,choices=(1,2))
    p.add_argument('--limit-new',type=int,default=1000)
    args=p.parse_args()
    if args.worker:
        print(json.dumps(worker(json.loads(args.worker)),separators=(',',':')))
        return
    BASE.mkdir(parents=True,exist_ok=True)
    checks=self_test()
    (BASE/'gram-self-test.json').write_text(json.dumps(checks,indent=2)+'\n',encoding='utf-8')
    cases=[make_case(40,n,q,h) for q in (4,5) for n in (1,3,6) for h in (20,28,40-n)]
    controls=[make_case(40,3,3,37,s) for s in (5,7)]
    known=load_known(); remaining=[args.limit_new]
    crows=run_stage(controls,known,args.workers,remaining)
    oldrows=[]
    for name in ('exact_sweep.jsonl','round2-results.jsonl'):
        oldrows += [json.loads(l) for l in (ROOT/'missions/zeta7/verification'/name).read_text(encoding='utf-8').splitlines()]
    for row in crows:
        matches=[r for r in oldrows if all(r.get(k)==row[k] for k in ('s','K','N','q','h')) and 'coefficients_sha256' in r]
        assert matches and all(r['coefficients_sha256']==row['coefficients_sha256'] for r in matches)
    rows=run_stage(cases,known,args.workers,remaining)
    promoted=[]
    if len(rows)==len(cases):
        ranked=sorted(rows,key=lambda r:(r['log_value_per_K2'],r['q'],r['h'],r['case_id']))
        # Retain full ball evidence; verify the scheduling cutoff is separated.
        from flint import arb,ctx
        def ball(v): return arb(v['mid'],v['rad'])*arb(10)**v['exp']
        with ctx.workprec(256):
            assert ball(ranked[2]['log_interval']).upper()<ball(ranked[3]['log_interval']).lower()
        promoted=[make_case(80,r['n40'],r['q'],r['h40'],source=r['case_id']) for r in ranked[:3]]
        run_stage(promoted,known,args.workers,remaining)
    manifest=dict(description='18 K40 zeta9 controls, top3 K80; not an asymptotic proof',
                  cases=cases,regression_controls=controls,promoted=promoted,
                  timeout_seconds=120,workers=args.workers)
    (BASE/'gram-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print('saved gram manifest; successful',sum(r.get('status')=='ok' for r in known.values()),flush=True)


if __name__=='__main__':
    main()
