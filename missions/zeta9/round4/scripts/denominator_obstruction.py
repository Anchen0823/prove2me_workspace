"""Finite primitive lower bounds from large-prime residues and direct Arb sums.

No full rational constant B or its exact denominator is computed here.
For p in (Dn,2Dn), p^9 B == -D^9 sum_{j>=ceil(p/D)-n} C_j mod p.
If this is nonzero, p^9 divides the reduced denominator of B.  Thus
Q product of those p^9 gives |primitive(L)| >= Q*|L|/|A| when A != 0.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'tmp/zeta7/exact_packages'))
sys.set_int_max_str_digits(0)
from flint import arb,ctx,fmpq,fmpz

OUT=ROOT/'missions/zeta9/round4/verification'
WEIGHTS={6:([1,2,3,6],[-7776,1701,-224,1]),
         8:([1,2,4,8],[-32768,5376,-168,1])}


def iv(x):
    mid,rad,exp=x.mid_rad_10exp(50)
    return dict(mid=str(mid),rad=str(rad),exp=int(exp))


def pair(q):
    return [str(q.numer()),str(q.denom())]


def primes(limit):
    sieve=bytearray(b'\1')*(limit+1)
    sieve[:2]=b'\0\0'
    for p in range(2,math.isqrt(limit)+1):
        if sieve[p]:
            sieve[p*p::p]=b'\0'*(((limit-p*p)//p)+1)
    return [p for p in range(2,limit+1) if sieve[p]]


def highest(n):
    return [(-1)**j*math.comb(n,j)**9*math.comb(n+j,n)*math.comb(2*n-j,n)
            for j in range(n+1)]


def first_term(D,n,a):
    # t=n+a/D, using the original finite product, all factors positive.
    arg=D*n+a
    numerator=math.factorial(n)**7*D**(7*n+9)
    numerator*=math.prod(arg-D*j for j in range(1,n+1))
    numerator*=math.prod(arg+D*(n+j) for j in range(1,n+1))
    denominator=math.prod((arg+D*j)**9 for j in range(n+1))
    return fmpq(numerator,denominator)


def ratio(D,n,k,a):
    # Exact rational ratio R(t+1)/R(t), t=k+a/D.
    arg=D*k+a
    return fmpq(arg**10*(arg+D*(2*n+1)),
                (arg-D*n)*(arg+D*(n+1))**10)


def direct_raw(D,n,bits=1024):
    divisors,weights=WEIGHTS[D]
    folded=[sum(w for d,w in zip(divisors,weights) if (a*d)%D==0)
            for a in range(1,D+1)]
    T=4*n
    F=fmpq(math.factorial(n)**7)
    delta=7*n+9
    with ctx.workprec(bits):
        total=arb(0)
        radius=fmpq(0)
        rows=[]
        for a,w in enumerate(folded,1):
            term=arb(first_term(D,n,a))
            finite=arb(0)
            for k in range(n,T+1):
                finite+=term
                if k<T:
                    term*=arb(ratio(D,n,k,a))
            x=fmpq(D*T+a,D)
            tail=F*(1+fmpq(2*n)/x)**(2*n)/((delta-1)*x**(delta-1))
            total+=w*finite
            radius+=abs(w)*tail
            rows.append(dict(a=a,weight=w,finite_interval=iv(finite),tail_bound=pair(tail)))
        value=total+arb(0,arb(radius).upper())
        sign=1 if value.lower()>0 else (-1 if value.upper()<0 else 0)
        assert sign!=0,(D,n,str(value))
        absolute=value if sign==1 else -value
        return dict(interval=iv(value),sign=sign,log_abs=iv(absolute.log()),
                    total_tail_radius=pair(radius),shift_rows=rows,
                    bits=bits,T=T), absolute


def run(D,n):
    assert D in WEIGHTS and n>=4 and n%2==0
    start=time.monotonic()
    coefficients=highest(n)
    suffix=[0]*(n+2)
    for j in range(n,-1,-1):
        suffix[j]=suffix[j+1]+coefficients[j]
    divisors,weights=WEIGHTS[D]
    kappa=sum(w*d**9 for d,w in zip(divisors,weights))
    assert all(sum(w*d**s for d,w in zip(divisors,weights))==0 for s in (3,5,7))
    A=kappa*suffix[0]
    # Do not infer universal nonvanishing from the finite exact check.
    assert A!=0,(D,n)
    kept=[]
    local=[]
    for p in primes(2*D*n):
        if p<=D*n:
            continue
        assert p>2*n and p*p>2*D*n and D%p!=0
        j0=(p+D-1)//D-n
        residue=(-pow(D,9,p)*(suffix[j0]%p))%p
        local.append(dict(p=p,j0=j0,residue=residue,forced_denominator_order=9 if residue else None))
        if residue:
            kept.append(p)
    Q=math.prod(p**9 for p in kept)
    raw,absolute=direct_raw(D,n)
    with ctx.workprec(1024):
        bound=arb(fmpz(Q))*absolute/arb(fmpz(abs(A)))
        assert bound.lower()>1,(D,n,str(bound))
        logbound=bound.log()
        result=dict(D=D,n=n,m=n,status='finite_primitive_abs_greater_than_one_certified',
             theorem='Q divides denominator(B); A integer nonzero; primitive multiplier >= Q/abs(A)',
             A=str(A),A_sign=1 if A>0 else -1,Q=str(Q),
             highest_coefficients=[str(v) for v in coefficients],
             local_primes=local,forced_primes=kept,prime_count=len(local),
             forced_prime_count=len(kept),
             log_Q_per_n=iv(arb(fmpz(Q)).log()/n),
             log_abs_A_per_n=iv(arb(fmpz(abs(A))).log()/n),
             log_raw_abs_per_n=iv(absolute.log()/n),
             primitive_abs_lower_bound=iv(bound),
             primitive_log_lower_per_n=iv(logbound/n),
             primitive_log_lower_per_n_display=float(logbound/n),
             raw=raw,seconds=time.monotonic()-start,
             source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    OUT.mkdir(parents=True,exist_ok=True)
    path=OUT/f'obstruction-D{D}-n{n}.json'
    path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    return dict(D=D,n=n,status=result['status'],forced=len(kept),available=len(local),
                log_lower_per_n=float(logbound/n),seconds=result['seconds'],
                artifact=str(path.relative_to(ROOT)),sha256=hashlib.sha256(path.read_bytes()).hexdigest())


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n',type=int,nargs='+',default=[24,48,96,192,384])
    args=parser.parse_args()
    rows=[]
    for n in args.n:
        for D in (6,8):
            row=run(D,n)
            rows.append(row)
            print(json.dumps(row),flush=True)
    (OUT/'obstruction-index.json').write_text(json.dumps(rows,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':
    main()
