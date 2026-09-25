"""Independent finite denominator certificate using exact assignment duals.

For G=A+XB and w_ij=min(v_p(A_ij),v_p(B_ij)), every coefficient
of det G has valuation >= min_pi sum_i w_i,pi(i). Exact integer
Hungarian primal/dual witnesses certify that minimum, including small primes.
This finite certificate is NOT an asymptotic bound.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import gzip
import json
import math
from pathlib import Path
import time
from exact_hankel import ROOT, parameters
from flint import arb, ctx, fmpz, fmpq_poly, fmpq_mat


def primes_to(n):
    sieve = bytearray(b'\1')*(n+1)
    sieve[:2] = b'\0\0'
    for p in range(2, math.isqrt(n)+1):
        if sieve[p]:
            sieve[p*p:n+1:p] = b'\0'*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if sieve[p]]


def vp(n, p):
    if n == 0:
        return None
    value = 0
    while n % p == 0:
        n //= p
        value += 1
    return value


def rational_vp(pair, p):
    num, den = pair
    a = vp(num, p)
    return None if a is None else a-vp(den,p)


def assignment(w):
    """Exact O(n^3) Hungarian with verified dual feasibility/equality."""
    n = len(w)
    u,v,p,way = [0]*(n+1),[0]*(n+1),[0]*(n+1),[0]*(n+1)
    for i in range(1,n+1):
        p[0]=i
        j0=0
        minv=[None]*(n+1)
        used=[False]*(n+1)
        while True:
            used[j0]=True
            i0=p[j0]
            delta=None
            j1=0
            for j in range(1,n+1):
                if used[j]:
                    continue
                cur=w[i0-1][j-1]-u[i0]-v[j]
                if minv[j] is None or cur<minv[j]:
                    minv[j]=cur
                    way[j]=j0
                if delta is None or minv[j]<delta:
                    delta,j1=minv[j],j
            for j in range(n+1):
                if used[j]:
                    u[p[j]]+=delta
                    v[j]-=delta
                elif minv[j] is not None:
                    minv[j]-=delta
            j0=j1
            if p[j0]==0:
                break
        while True:
            j1=way[j0]
            p[j0]=p[j1]
            j0=j1
            if not j0:
                break
    perm=[0]*n
    for j in range(1,n+1):
        perm[p[j]-1]=j-1
    total=sum(w[i][perm[i]] for i in range(n))
    assert sorted(perm)==list(range(n))
    assert total==sum(u[1:])+sum(v[1:])
    assert all(u[i+1]+v[j+1]<=w[i][j] for i in range(n) for j in range(n))
    return dict(lower_bound=total, permutation=perm, row_dual=u[1:], column_dual=v[1:])


def certify(row, basis='monomial'):
    start=time.monotonic()
    K,h,s=row['K'],row['h'],row['s']
    zeros={int(j):m for j,m in row['zero_multiplicities'].items()}
    exps=row['exponents']
    result=parameters(s,K,0,0,h,zeros,exps)
    # Reconstruct from input rather than trust saved coefficients.
    if 'primitive_coefficients_ascending' in row:
        assert result['coeffs']==row['primitive_coefficients_ascending']
    max_moment=max(0,2*sum(zeros.values())-K+2*max(exps))
    # Monic polynomial division introduces no denominators. Tail residues
    # divide products of j^2-l^2, whose prime factors <=2K. Pole constants
    # use H_j^(s), (s-1),2j. Bernoulli denominators have p<=2e+3.
    prime_limit=max(2*K,2*max_moment+3,s-1)
    A,B=result['A'],result['B']
    if basis == 'newton':
        if exps != list(range(exps[0],exps[0]+h)):
            raise ValueError('Newton transform requires a whole shifted block')
        # u_0=1, u_i=t product_{j=1}^{i-1}(t+j^2) is monic integral.
        # The matrix T is unit lower triangular, so Delta is unchanged.
        t=fmpq_poly([0,1])
        poly=fmpq_poly([1])
        coeffrows=[]
        for i in range(h):
            if i:
                poly *= t+(i-1)**2
            coeffrows.append([poly[j] for j in range(h)])
        T=fmpq_mat(coeffrows)
        assert all(T[i,i]==1 and all(T[i,j]==0 for j in range(i+1,h)) for i in range(h))
        A,B=T*A*T.transpose(),T*B*T.transpose()
    elif basis != 'monomial':
        raise ValueError('Unknown basis')
    entry_keys={}
    matrix_keys=[]
    for i in range(h):
        rowkeys=[]
        for j in range(h):
            a,b=A[i,j],B[i,j]
            key=((int(a.numer()),int(a.denom())),(int(b.numer()),int(b.denom())))
            if key not in entry_keys:
                entry_keys[key]=len(entry_keys)
            rowkeys.append(entry_keys[key])
        matrix_keys.append(rowkeys)
    keys=list(entry_keys)
    local=[]
    multiplier=Fraction(1)
    for p in primes_to(prime_limit):
        values=[]
        for a,b in keys:
            va,vb=rational_vp(a,p),rational_vp(b,p)
            finite=[x for x in (va,vb) if x is not None]
            values.append(min(finite) if finite else None)
        M=max([abs(v) for v in values if v is not None]+[1])
        # Diagonal is finite because G(zeta)>0. A sentinel exceeding all
        # finite matching costs cannot occur in an optimal assignment.
        cap=(2*h+1)*M+1
        w=[[cap if values[k] is None else values[k] for k in r] for r in matrix_keys]
        witness=assignment(w)
        assert all(values[matrix_keys[i][j]] is not None for i,j in enumerate(witness['permutation']))
        lower=witness['lower_bound']
        actual=min(vp(c,p) for c in result['delta'].numer() if c)-vp(int(result['delta'].denom()),p)
        assert lower<=actual
        if lower>=0:
            multiplier/=p**lower
        else:
            multiplier*=p**(-lower)
        local.append(dict(p=p, actual_minimum=actual, slack=actual-lower, **witness))
    scale=Fraction(int(result['primitive_scale'].numer()),int(result['primitive_scale'].denom()))
    gap=multiplier/scale
    assert gap.denominator==1 and gap.numerator>=1
    with ctx.workprec(256):
        gap_log=arb(fmpz(gap.numerator)).log()/(K*K)
        mid,rad,exp=gap_log.mid_rad_10exp(35)
        gap_interval=dict(mid=str(mid),rad=str(rad),exp=int(exp))
    return dict(case_id=row['case_id'], K=K,h=h, basis=basis,prime_limit=prime_limit,
                multiplier_numerator=multiplier.numerator,multiplier_denominator=multiplier.denominator,
                gap_integer=gap.numerator, gap_log_per_K2=float(gap_log),
                gap_log_per_K2_interval=gap_interval, local=local,
                certified_finite_integerization=True, asymptotic_certificate=False,
                primitive_scale_verified=True, seconds=time.monotonic()-start)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--case-id',action='append',required=True)
    p.add_argument('--basis',choices=('monomial','newton'),default='monomial')
    p.add_argument('--out',default='missions/zeta7/verification/round2-entry-certificates.json')
    args=p.parse_args()
    rows=[]
    for case_id in args.case_id:
        artifact=ROOT/'missions/zeta7/verification/round2-coeff'/f'{case_id}.json.gz'
        with gzip.open(artifact,'rt',encoding='utf-8') as f:
            row=json.load(f)
        cert=certify(row,args.basis)
        rows.append(cert)
        print(json.dumps({k:v for k,v in cert.items() if k not in ('local','gap_integer','multiplier_numerator','multiplier_denominator')},indent=2),flush=True)
        (ROOT/args.out).write_text(json.dumps(rows,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':
    main()
