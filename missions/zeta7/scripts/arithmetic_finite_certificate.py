"""Finite coefficientwise determinant certificates for multilayer zeta(7) matrices.

No asymptotic A is used.  The certificate multiplier t satisfies t*Delta in Z[X].
Proof: research/round2-arithmetic.md.  The implementation uses only integer and
rational arithmetic; float logs are reporting aids, never proof inputs.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)


def primes_up_to(n: int) -> list[int]:
    flags = bytearray(b'\x01')*(n+1)
    if n >= 0: flags[0] = 0
    if n >= 1: flags[1] = 0
    for p in range(2, math.isqrt(n)+1):
        if flags[p]:
            flags[p*p:n+1:p] = b'\x00'*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if flags[p]]


def vp(n: int, p: int):
    if n == 0: return math.inf
    n = abs(n)
    result = 0
    while n % p == 0:
        result += 1
        n //= p
    return result


def vp_fraction(x: Fraction, p: int):
    return vp(x.numerator,p)-vp(x.denominator,p)


def factorial_valuations(limit: int, p: int) -> list[int]:
    out=[0]
    for n in range(1,limit+1):
        out.append(out[-1]+vp(n,p))
    return out


def moment_lower(e: int,p: int) -> int:
    # von Staudt--Clausen, with every factor in mu_7 kept.
    return (sum(vp(2*e+j,p) for j in range(3,8))-vp(720,p)
            -int((2*e+2)%(p-1)==0))


def convolve(a: list[int],b: list[int],cap: int) -> list[int]:
    c=[math.inf]*(min(cap,len(a)+len(b)-2)+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b[:cap-i+1]):
            if i+j < len(c): c[i+j]=min(c[i+j],x+y)
    return c


def vandermonde_dp(nodes: list[int],weights: list[int],p: int,cap: int) -> list[int]:
    """min sum weights+2 sum_{i<j}vp(nodes_i-nodes_j), for each cardinality."""
    def group_dp(indices, modulus):
        if len(indices)==1: return [0,weights[indices[0]]][:cap+1]
        groups={}
        for i in indices: groups.setdefault(nodes[i]%(modulus*p),[]).append(i)
        result=[0]
        for group in groups.values():
            result=convolve(result,group_dp(group,modulus*p),cap)
        return [cost+k*(k-1) for k,cost in enumerate(result)]
    groups={}
    for i,node in enumerate(nodes): groups.setdefault(node%p,[]).append(i)
    result=[0]
    for group in groups.values(): result=convolve(result,group_dp(group,p),cap)
    return result


def outer_bound(K:int,layers:list[tuple[int,int]],h:int,g:int,p:int,E:int):
    """Finite CRT bound; None means its explicit hypotheses are not satisfied."""
    Nmax=max((n for n,q in layers),default=0)
    if not (p>7 and p*p>2*K and 2*Nmax<p): return None
    counts={}
    for j in range(1,K+1):
        a=min(j%p,(-j)%p)
        counts[a]=counts.get(a,0)+1
    twice=[]
    for a,l in counts.items():
        if a==0:
            # Residue bound: 4g+2i+2j-2l+1. Polynomial mu_0 is only integral.
            twice.extend(min(0,4*g+4*i-2*l+1) for i in range(l))
            continue
        qa=sum(q for n,q in layers if a<=n)
        delta=int(qa>0)
        for i in range(l-delta):
            twice.append(min(0,2*i+2*qa-l-6) if i<l-2 else 0)
    assert len(twice)==K-Nmax
    if h>len(twice): twice.extend([0]*(h-len(twice)))
    chosen=sorted(twice)[:h]
    assert len(chosen)==h
    rank=min(h,max(0,E-3*p+5))
    return dict(bound=sum(chosen)-min(rank,chosen.count(0)),
                moment_rank=rank,negative_rows=sum(x<0 for x in chosen),
                zero_rows=chosen.count(0),twice_weights=chosen)


def certificate(K:int,layers:list[tuple[int,int]],h:int,g:int=0) -> dict:
    if K<1 or h<1 or g<0: raise ValueError('K,h>=1 and g>=0 required')
    layers=sorted((int(n),int(q)) for n,q in layers if n)
    if any(n<0 or n>=K or q<1 for n,q in layers):
        raise ValueError('Require 0<=N_a<K and q_a>=1')
    Nmax=max((n for n,q in layers),default=0)
    total=sum(n*q for n,q in layers)
    E=2*total-K+2*g+2*h-2
    rank_polynomial=min(h,max(0,E+1))
    prime_limit=max(7,2*K,2*E+3)
    integer_valued_degree=max(2*K,4*total+4*g+4*h+4)
    poles=list(range(Nmax+1,K+1))
    nodes=[-j*j for j in poles]
    harmonic=Fraction(0)
    pole_constant={}
    for j in range(1,K+1):
        harmonic+=Fraction(1,j**7)
        if j>Nmax:
            pole_constant[j]=-j**6*harmonic-Fraction(1,6)+Fraction(1,2*j)
    numerator=denominator=1
    rows=[]
    for p in primes_up_to(prime_limit):
        factorials=factorial_valuations(max(2*K,2*h),p)
        weights=[]
        for j in poles:
            jval=vp(j,p)
            # Exact residue valuation from the factorial product identity.
            residue=(vp(2,p)+2*jval-factorials[K-j]-factorials[K+j]
                     +2*sum(q*(factorials[j+n]-factorials[j-n-1]-jval)
                            for n,q in layers))
            affine=min(6*jval,vp_fraction(pole_constant[j],p))
            weights.append(residue+affine+4*g*jval)
        dp=vandermonde_dp(nodes,weights,p,min(h,len(poles)))
        beta=min((moment_lower(e,p) for e in range(E+1)),default=0)
        rank_moment=min(h,max(0,E-3*p+5)) if p>7 else None
        options=[]
        for k,residue_val in enumerate(dp):
            m=h-k
            if m>rank_polynomial: continue
            polynomial=m*beta
            if rank_moment is not None:
                polynomial=max(polynomial,-min(m,rank_moment))
            options.append((residue_val+polynomial,k))
        if not options: raise AssertionError('No determinant expansion term is available')
        bound_dp,k_best=min(options)
        outer=outer_bound(K,layers,h,g,p,E)
        scale_valuation=(2*h*factorials[K]+(h-1)*vp(4,p)
                         -4*h*sum(q*factorials[n] for n,q in layers)
                         -2*sum(factorials[2*i] for i in range(1,h)))
        logarithm=0
        power=p
        while power<=integer_valued_degree:
            logarithm+=1
            power*=p
        integer_valued_bound=-8*h*logarithm-h*vp(720,p)-scale_valuation
        # The logarithmic integer-valued estimate is retained for diagnosis only.
        # Its finite degree-dependent lemma has not been completed here; unlike
        # the mixed-minor and CRT bounds it must NOT affect a certificate.
        gamma=bound_dp
        if outer is not None: gamma=max(gamma,outer['bound'])
        gamma=int(gamma)
        if gamma<0: numerator*=p**(-gamma)
        else: denominator*=p**gamma
        rows.append(dict(p=p,moment_lower=beta,moment_rank=rank_moment,
                         mixed_minor_bound=bound_dp,mixed_residue_count=k_best,
                         crt_bound=None if outer is None else outer['bound'],
                         unproved_integer_valued_candidate=integer_valued_bound,
                         scale_valuation=scale_valuation,
                         gamma=gamma))
    multiplier=Fraction(numerator,denominator)
    return dict(kind='finite_coefficientwise_multiplier_for_Delta',s=7,K=K,h=h,g=g,
                layers=[dict(N=n,q=q) for n,q in layers],max_polynomial_moment=E,
                polynomial_rank_bound=rank_polynomial,prime_limit=prime_limit,
                integer_valued_degree_parameter=integer_valued_degree,
                multiplier_numerator=str(multiplier.numerator),
                multiplier_denominator=str(multiplier.denominator),
                log_multiplier_per_K2=(math.log(multiplier.numerator)-math.log(multiplier.denominator))/K**2,
                prime_bounds=rows,
                theorem='This exact rational multiplier times Delta belongs to Z[X].',
                disabled_candidates=['finite integer-valued 8 log D estimate'],
                reporting_logs_are_floating=True)


def compare_primitive(cert:dict,row:dict) -> dict:
    K,h,g=cert['K'],cert['h'],cert['g']
    assert row['K']==K and row['h']==h and row['s']==7
    assert row['exponents']==list(range(g,g+h))
    zeros={str(j):sum(a['q'] for a in cert['layers'] if j<=a['N'])
           for j in range(1,max((a['N'] for a in cert['layers']),default=0)+1)}
    assert row['zero_multiplicities']==zeros
    th=Fraction(int(cert['multiplier_numerator']),int(cert['multiplier_denominator']))
    prim=Fraction(int(row['primitive_scale_numerator']),int(row['primitive_scale_denominator']))
    ratio=th/prim
    assert ratio>0 and ratio.denominator==1, 'Finite certificate contradicts exact primitive scale'
    return dict(multiplier_over_primitive=str(ratio.numerator),ratio_is_positive_integer=True,
                log_ratio_per_K2=math.log(ratio.numerator)/K**2)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--K',type=int,default=40)
    ap.add_argument('--h',type=int,default=37)
    ap.add_argument('--g',type=int,default=0)
    ap.add_argument('--layers',default='3:4')
    ap.add_argument('--output',default='missions/zeta7/verification/arithmetic_finite_certificate.json')
    a=ap.parse_args()
    layers=[tuple(map(int,v.split(':'))) for v in a.layers.split(',') if v]
    cert=certificate(a.K,layers,a.h,a.g)
    out=Path(a.output);out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(cert,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in cert.items() if k not in
                     ('multiplier_numerator','multiplier_denominator','prime_bounds')},indent=2))


if __name__=='__main__': main()
