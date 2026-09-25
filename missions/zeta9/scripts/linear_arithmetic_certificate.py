"""Independent finite and asymptotic arithmetic for the zeta(9) linear forms.

All divisibility claims and asymptotic enclosures use integers/Fraction only.
Floating logarithms are reporting aids, not proof inputs. No determinants or
zeta evaluations are computed here. Proof: ../research/arithmetic.md.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import reduce
import gzip
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)


def primes_up_to(n):
    flags=bytearray(b'\x01')*(n+1)
    if n>=0: flags[0]=0
    if n>=1: flags[1]=0
    for p in range(2,math.isqrt(n)+1):
        if flags[p]: flags[p*p:n+1:p]=b'\x00'*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if flags[p]]


def vp(a,p):
    if a==0: raise ValueError('vp(0) is not needed by this certificate')
    a=abs(a); v=0
    while a%p==0: a//=p; v+=1
    return v


def vp_factorial(n,p):
    result=0
    while n:
        n//=p
        result+=n
    return result


def vp_c(n,m,j,p):
    return (3*vp_factorial(n,p)+7*vp_factorial(j+m,p)
            +7*vp_factorial(n-j+m,p)-10*vp_factorial(j,p)
            -10*vp_factorial(n-j,p)-14*vp_factorial(m,p))


def validate(n,m):
    if n<2 or n%2 or m<0 or 14*m>3*n+1:
        raise ValueError('Require even n>=2, m>=0, and 14m<=3n+1; m=0 is a control')


def finite_certificate(n,m):
    validate(n,m)
    coefficients=[(-1)**(m+j)*math.comb(n,j)**3
                  *math.comb(j+m,m)**7*math.comb(n-j+m,m)**7
                  for j in range(n+1)]
    common=reduce(math.gcd,coefficients)
    lcm=1
    rows=[]
    for p in primes_up_to(n+m):
        power=p; exponent=0
        while power<=n+m:
            exponent+=1
            power*=p
        lcm*=p**exponent
        via_floor=min(vp_c(n,m,j,p) for j in range(n+1))
        actual=vp(common,p)
        assert via_floor==actual
        large=None
        if p*p>n+m:
            large=7*int((n%p)+2*(m%p)>=2*p-1)
            assert large==actual
        rows.append(dict(p=p,lcm_exponent=exponent,
                         common_exponent=actual,large_prime_formula=large,
                         multiplier_exponent=int(p==2)+9*exponent-actual))
    multiplier=Fraction(2*lcm**9,common)
    return dict(n=n,m=m,alpha=str(Fraction(m,n)),
                common_C_gcd=str(common),lcm=str(lcm),
                multiplier_numerator=str(multiplier.numerator),
                multiplier_denominator=str(multiplier.denominator),
                log_multiplier_per_n=(math.log(multiplier.numerator)-math.log(multiplier.denominator))/n,
                log_common_gcd_per_n=math.log(common)/n,
                A=str(28*sum(coefficients)),prime_bounds=rows,
                theorem='multiplier*(A*zeta(9)+B) has integer coefficients',
                logs_are_floating=True)


def improved_certificate(n,m):
    """The stronger d_n^9/G multiplier, independently derived in section 2.1."""
    base=finite_certificate(n,m)
    common=int(base['common_C_gcd'])
    lcm_n=1
    for k in range(1,n+1): lcm_n=math.lcm(lcm_n,k)
    multiplier=Fraction(lcm_n**9,common)
    old=Fraction(int(base['multiplier_numerator']),int(base['multiplier_denominator']))
    improvement=old/multiplier
    assert improvement.denominator==1
    rows=[]
    for row in base['prime_bounds']:
        p=row['p']; power=p; exponent=0
        while power<=n:
            exponent+=1
            power*=p
        rows.append(dict(p=p,lcm_n_exponent=exponent,
                         common_exponent=row['common_exponent'],
                         multiplier_exponent=9*exponent-row['common_exponent']))
    return dict(n=n,m=m,alpha=str(Fraction(m,n)),
                common_C_gcd=str(common),lcm_n=str(lcm_n),
                multiplier_numerator=str(multiplier.numerator),
                multiplier_denominator=str(multiplier.denominator),
                old_multiplier_over_new=str(improvement.numerator),
                log_multiplier_per_n=(math.log(multiplier.numerator)-math.log(multiplier.denominator))/n,
                old_log_multiplier_per_n=base['log_multiplier_per_n'],
                A=base['A'],prime_bounds=rows,
                theorem='d_n^9/G times (A*zeta(9)+B) has integer coefficients',
                logs_are_floating=True)


def compare_exact(cert,row):
    """Read-only comparison against independent exact-agent coefficients."""
    with gzip.open(row['artifact_path'],'rt',encoding='utf-8') as stream:
        exact=json.load(stream)
    A=Fraction(*map(int,exact['A_zeta_rational']))
    B=Fraction(*map(int,exact['B_constant_rational']))
    assert A==int(cert['A'])
    assert int(exact['G_residue_gcd'])==int(cert['common_C_gcd'])
    multiplier=Fraction(int(cert['multiplier_numerator']),int(cert['multiplier_denominator']))
    primitive=Fraction(*map(int,exact['primitive_multiplier']))
    assert (multiplier*A).denominator==(multiplier*B).denominator==1
    ratio=multiplier/primitive
    assert ratio>0 and ratio.denominator==1
    a,b=map(int,exact['primitive_integer_coefficients'])
    assert primitive*A==a and primitive*B==b and math.gcd(a,b)==1
    gap=math.log(ratio.numerator)/cert['n']
    return dict(case_id=row['case_id'],artifact_path=row['artifact_path'],
                multiplier_over_primitive=str(ratio.numerator),
                multiplier_over_primitive_is_positive_integer=True,
                log_gap_per_n=gap,
                primitive_log_scale_per_n=(math.log(primitive.numerator)-math.log(primitive.denominator))/cert['n'],
                primitive_abs_log_per_n_reported=row['abs_log_per_n'],
                improved_form_abs_log_per_n_proxy=row['abs_log_per_n']+gap,
                both_scaled_coefficients_are_integers=True)


def periodic_intervals(alpha):
    """Intervals on one period where {x}+2{alpha*x}>=2, endpoints immaterial."""
    alpha=Fraction(alpha)
    if not (0<alpha<=Fraction(3,14)): raise ValueError('0<alpha<=3/14 required')
    period=alpha.denominator
    cuts={Fraction(k) for k in range(period+1)}
    cuts.update(Fraction(k,1)/alpha for k in range(alpha.numerator+1))
    cuts=sorted(cuts)
    intervals=[]
    for left,right in zip(cuts,cuts[1:]):
        middle=(left+right)/2
        a=math.floor(middle);b=math.floor(alpha*middle)
        start=max(left,Fraction(a+2*b+2,1)/(1+2*alpha))
        if start<right:
            if intervals and intervals[-1][1]==start:
                intervals[-1]=(intervals[-1][0],right)
            else: intervals.append((start,right))
    assert all(left>0 for left,right in intervals)
    return period,intervals


def arithmetic_limit(alpha,periods=4096,digits=32):
    """Exact rational enclosure of Gamma and 9(1+alpha)-Gamma.

    Reciprocals are rounded outwards onto a fixed integer lattice. Periodic
    tail bounds use only integral comparisons for sum(1/r^2).
    """
    alpha=Fraction(alpha)
    if periods<1 or digits<1: raise ValueError('positive periods and digits required')
    period,intervals=periodic_intervals(alpha)
    measure=sum((b-a for a,b in intervals),Fraction(0))
    scale=10**digits
    lower=upper=0
    def reciprocal_bounds(x):
        numerator=scale*x.denominator
        quotient,remainder=divmod(numerator,x.numerator)
        return quotient,quotient+int(remainder!=0)
    for r in range(periods):
        for a,b in intervals:
            la,ua=reciprocal_bounds(a+r*period)
            lb,ub=reciprocal_bounds(b+r*period)
            lower+=la-ub
            upper+=ua-lb
    tail_lower=measure/Fraction(period**2*(periods+1))
    tail_upper=measure/Fraction(period**2)*(Fraction(1,periods)+Fraction(1,periods**2))
    gamma_lower=7*(Fraction(lower,scale)+tail_lower)
    gamma_upper=min(7*(Fraction(upper,scale)+tail_upper),14*alpha)
    cost_lower=9*(1+alpha)-gamma_upper
    cost_upper=9*(1+alpha)-gamma_lower
    sharp_lower=9-gamma_upper
    sharp_upper=9-gamma_lower
    assert 0<=gamma_lower<=gamma_upper<=14*alpha
    return dict(alpha=str(alpha),period=period,periods_summed=periods,
                intervals=[[str(a),str(b)] for a,b in intervals],
                measure_per_period=str(measure),
                gamma_lower=str(gamma_lower),gamma_upper=str(gamma_upper),
                cost_lower=str(cost_lower),cost_upper=str(cost_upper),
                improved_cost_lower=str(sharp_lower),improved_cost_upper=str(sharp_upper),
                gamma_decimal_interval=[float(gamma_lower),float(gamma_upper)],
                cost_decimal_interval=[float(cost_lower),float(cost_upper)],
                improved_cost_decimal_interval=[float(sharp_lower),float(sharp_upper)],
                theorem='log(G)/n tends to Gamma; log(multiplier)/n tends to 9*(1+alpha)-Gamma',
                exact_enclosure=True)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',default='missions/zeta9/verification/arithmetic-certificates.json')
    ap.add_argument('--periods',type=int,default=4096)
    ap.add_argument('--improved',action='store_true')
    ap.add_argument('--compare-exact',help='Read an existing exact-results JSONL; requires --improved')
    args=ap.parse_args()
    finite=[]
    existing={}
    if args.compare_exact:
        if not args.improved: raise ValueError('--compare-exact requires --improved')
        for line in Path(args.compare_exact).read_text(encoding='utf-8').splitlines():
            row=json.loads(line)
            if row.get('status')=='ok' and row.get('s')==9:
                existing[(row['n'],row['m'])]=row
        cases=sorted(existing)
    else:
        cases=[(n,a*n//28) for n in (56,112,224) for a in range(1,7)]
    for n,m in cases:
        result=(improved_certificate if args.improved else finite_certificate)(n,m)
        if (n,m) in existing: result['primitive_comparison']=compare_exact(result,existing[(n,m)])
        finite.append(result)
        summary={k:result[k] for k in ('n','m','alpha','log_multiplier_per_n')}
        if 'primitive_comparison' in result:
            summary['gap_per_n']=result['primitive_comparison']['log_gap_per_n']
        print(json.dumps(summary),flush=True)
    limits=[arithmetic_limit(Fraction(a,28),args.periods) for a in range(1,7)]
    for result in limits:
        print(json.dumps({k:result[k] for k in
                          ('alpha','gamma_decimal_interval','cost_decimal_interval','improved_cost_decimal_interval')}),flush=True)
    out=Path(args.output)
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(dict(finite=finite,limits=limits),indent=2)+'\n',encoding='utf-8')


if __name__=='__main__': main()
