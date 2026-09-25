"""Read stored coefficients and independently evaluate with even/odd Arb Horner."""
from __future__ import annotations
import gzip
import argparse
import hashlib
import json
import math
import sys
from pathlib import Path
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'tmp/zeta7/exact_packages'))
from flint import arb,ctx,fmpz


def horner(cs,x):
    v=arb(0)
    for c in reversed(cs):
        v=v*x+fmpz(c)
    return v


def main():
    directory=ROOT/'missions/zeta7/verification'
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',default='round2-results.jsonl')
    parser.add_argument('--output',default='round2-independent-audit.json')
    args=parser.parse_args()
    latest={}
    for line in (directory/args.input).read_text(encoding='utf-8').splitlines():
        row=json.loads(line)
        latest[row['case_id']]=row
    verified=[]
    for case,row in latest.items():
        if row['status']!='ok':
            continue
        path=ROOT/row['artifact_path']
        assert hashlib.sha256(path.read_bytes()).hexdigest()==row['artifact_sha256']
        with gzip.open(path,'rt',encoding='utf-8') as f:
            full=json.load(f)
        cs=full['primitive_coefficients_ascending']
        assert hashlib.sha256(','.join(map(str,cs)).encode()).hexdigest()==row['coefficients_sha256']
        assert math.gcd(*cs)==1
        assert len(cs)-1==row['degree'] and cs[-1]!=0
        bits=max(row['arb_bits'],512)
        for attempt in range(4):
            with ctx.workprec(bits):
                z=arb(row['s']).zeta()
                value=horner(cs[::2],z*z)+z*horner(cs[1::2],z*z)
                if value.lower()>0 and value.rel_accuracy_bits()>=80:
                    saved=row['log_interval']
                    ball=arb(saved['mid'],saved['rad'])*arb(10)**saved['exp']
                    assert value.log().overlaps(ball)
                    below=bool(value.upper()<1)
                    above=bool(value.lower()>1)
                    assert below or above
                    assert above if row['s']==7 else below
                    verified.append(dict(case_id=case,s=row['s'],K=row['K'],degree=row['degree'],
                                         coefficients_sha256=row['coefficients_sha256'],
                                         primitive=True,positive=True,below_one=below,
                                         bits=bits,relative_accuracy_bits=value.rel_accuracy_bits(),
                                         agrees_with_saved_log=True))
                    break
            bits*=2
        else:
            raise ArithmeticError(f'Independent evaluation unresolved for {case}')
    summary=dict(successful=len(verified),zeta7_above_one=sum(r['s']==7 and not r['below_one'] for r in verified),
                 zeta5_below_one=sum(r['s']==5 and r['below_one'] for r in verified),
                 unresolved=[dict(case_id=r['case_id'],error=r.get('error')) for r in latest.values() if r['status']!='ok'],
                 verification='Independent even/odd evaluation of saved full coefficients; exact gcd and SHA.',
                 records=verified)
    (directory/args.output).write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in summary.items() if k!='records'},indent=2))


if __name__=='__main__':
    main()
