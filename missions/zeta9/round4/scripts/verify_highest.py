"""Exact sanity checks for the proved highest-coefficient lemma; not its proof."""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'tmp/zeta7/exact_packages'))
from flint import fmpq,fmpq_poly


def main():
    records=[]
    z=fmpq_poly([0,1])
    for n in range(2,41,2):
        # Rodrigues and the fractional-linear change of variables,
        # computed as exact polynomial operations.
        rod=(z*z-1)**n
        for _ in range(n):
            rod=rod.derivative()
        rod*=fmpq(1,2**n*math.factorial(n))
        transformed=fmpq_poly([0])
        for j in range(n+1):
            transformed+=rod[j]*(1+z)**j*(1-z)**(n-j)
        assert transformed==fmpq_poly([math.comb(n,j)**2 for j in range(n+1)])
        coefficients=[math.comb(n,j) for j in range(n+1)]
        for _ in range(8):
            coefficients=[c*math.comb(n,j) for j,c in enumerate(coefficients)]
        for k in range(1,n+1):
            coefficients=[c*(j+k) for j,c in enumerate(coefficients)]
        assert all(c%math.factorial(n)==0 for c in coefficients)
        coefficients=[c//math.factorial(n) for c in coefficients]
        for k in range(n+1,2*n+1):
            coefficients=[c*(k-j) for j,c in enumerate(coefficients)]
        assert all(c%math.factorial(n)==0 for c in coefficients)
        coefficients=[c//math.factorial(n) for c in coefficients]
        expected=[math.comb(n,j)**9*math.comb(n+j,n)*math.comb(2*n-j,n)
                  for j in range(n+1)]
        assert coefficients==expected==expected[::-1]
        rho=sum((-1)**j*c for j,c in enumerate(coefficients))
        assert (-1)**(n//2)*rho>0
        records.append(dict(n=n,rho=str(rho),sign=(-1)**(n//2),
                            Rodrigues_identity=True,operator_identity=True,palindromic=True))
    output=ROOT/'missions/zeta9/round4/verification/highest-audit.json'
    output.write_text(json.dumps(dict(status='ok',cases=len(records),rows=records,
        scope='finite exact sanity checks; universal nonvanishing is established in the proof note',
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='ok',cases=len(records),output=str(output))))


if __name__=='__main__':
    main()
