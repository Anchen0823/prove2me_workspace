"""Finite all-prime denominator certificates for the best zeta9 Gram profile.

Reuses the generic exact assignment proof, without s=7 asymptotic constants.
Every prime's primal/dual witness is saved; no asymptotic claim is made.
"""
import gzip
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'missions/zeta7/scripts'))
from round2_entry_certificate import certify

BASE=ROOT/'missions/zeta9/verification'


def main():
    rows=[]
    for case in ('s9-K40-N6-q4-h20','s9-K80-N12-q4-h40'):
        with gzip.open(BASE/'gram-coeff'/f'{case}.json.gz','rt',encoding='utf-8') as f:
            full=json.load(f)
        for basis in ('monomial','newton'):
            row=certify(full,basis)
            rows.append(row)
            (BASE/'gram-arithmetic-certificates.json').write_text(
                json.dumps(rows,indent=2)+'\n',encoding='utf-8')
            print(json.dumps({k:row[k] for k in
                ('case_id','basis','prime_limit','gap_log_per_K2','seconds')}),flush=True)


if __name__=='__main__':
    main()
