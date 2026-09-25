"""Root-agent cross-checks using direct Taylor series and exact polynomial identities.

The finite Taylor sum is formed from R itself, without partial fractions.
Its tail uses an independently verified partial-fraction identity and the
integral test. This is finite evidence, not an asymptotic nonvanishing proof.
"""
from __future__ import annotations
from fractions import Fraction
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'tmp/zeta7/exact_packages'))
sys.set_int_max_str_digits(0)
from flint import arb, ctx, fmpq, fmpq_poly, fmpz
from odd_linear_form import exact_form, interval

OUT = ROOT/'missions/zeta9/verification'


def ball(obj):
    return arb(obj['mid'], obj['rad'])*arb(10)**obj['exp']


def gram_audit():
    verified=[]
    for line in (OUT/'gram-results.jsonl').read_text(encoding='utf-8').splitlines():
        short=json.loads(line)
        assert short['status']=='ok'
        path=ROOT/short['artifact_path']
        assert hashlib.sha256(path.read_bytes()).hexdigest()==short['artifact_sha256']
        with gzip.open(path,'rt',encoding='utf-8') as f:
            row=json.load(f)
        cs=row['primitive_coefficients_ascending']
        assert math.gcd(*cs)==1 and len(cs)==row['degree']+1
        digest=hashlib.sha256(','.join(map(str,cs)).encode()).hexdigest()
        assert digest==row['coefficients_sha256']==short['coefficients_sha256']
        assert Fraction(row['denominator'],row['numerator_content'])==Fraction(
            row['primitive_scale_numerator'],row['primitive_scale_denominator'])
        with ctx.workprec(row['arb_bits']+256):
            z=arb(row['s']).zeta()
            # Split even/odd powers, independent of the original single Horner chain.
            parts=[]
            for parity in (0,1):
                value=arb(0)
                for c in reversed(cs[parity::2]):
                    value=value*z*z+fmpz(c)
                parts.append(value)
            value=parts[0]+z*parts[1]
            assert value.lower()>0 and value.overlaps(ball(row['P_interval']))
            logv=value.log()
            assert logv.overlaps(ball(row['log_interval']))
            if row['s']==9:
                assert logv.lower()>0
        verified.append(dict(case_id=row['case_id'], coefficient_hash=digest,
                             positive=True, value_ball_overlap=True,
                             primitive_gcd=1, above_one=(row['s']!=5)))
    return verified


def multiply_truncated(a,b,order):
    return [sum((a[i]*b[j-i] for i in range(max(0,j-len(b)+1),min(j,len(a)-1)+1)),fmpq(0))
            for j in range(min(order+1,len(a)+len(b)-1))]


def direct_taylor(n,m,s,k):
    order=s-3
    numerator=[fmpq(1)]
    denominator=[fmpq(1)]
    for shift in list(range(-m,0))+list(range(n+1,n+m+1)):
        factor=[fmpq(math.comb(s-2,i)*(k+shift)**(s-2-i)) for i in range(order+1)]
        numerator=multiply_truncated(numerator,factor,order)
    for shift in range(n+1):
        factor=[fmpq(math.comb(3,i)*(k+shift)**(3-i)) for i in range(4)]
        denominator=multiply_truncated(denominator,factor,order)
    numerator += [fmpq(0)]*(order+1-len(numerator))
    denominator += [fmpq(0)]*(order+1-len(denominator))
    quotient=[]
    for j in range(order+1):
        quotient.append((numerator[j]-sum((denominator[i]*quotient[j-i]
                                          for i in range(1,j+1)),fmpq(0)))/denominator[0])
    return quotient[order]*fmpq(math.factorial(n)**3,math.factorial(m)**(2*(s-2)))


def direct_sum_audit(n,m,s=9,T=256):
    start=time.monotonic()
    form=exact_form(s,n,m)
    x=fmpq_poly([0,1])
    denom=fmpq_poly([1])
    numer=fmpq_poly([1])
    for j in range(n+1):
        denom *= (x+j)**3
    for shift in list(range(-m,0))+list(range(n+1,n+m+1)):
        numer *= (x+shift)**(s-2)
    numer *= fmpq(math.factorial(n)**3,math.factorial(m)**(2*(s-2)))
    reconstructed=fmpq_poly([0])
    for j in range(n+1):
        for order,c in ((1,form['c1'][j]),(2,form['c2'][j]),(3,fmpq(form['C'][j]))):
            q,r=divmod(denom,(x+j)**order)
            assert not r
            reconstructed += c*q
    assert numer==reconstructed
    finite=sum((direct_taylor(n,m,s,k) for k in range(1,T+1)),fmpq(0))
    top=math.comb(s-1,2)
    radius=sum((abs(form['c1'][j])/((s-3)*(T+j)**(s-3))
                +(s-2)*abs(form['c2'][j])/((s-2)*(T+j)**(s-2))
                +top*abs(form['C'][j])*fmpq(1,(s-1)*(T+j)**(s-1))
                for j in range(n+1)),fmpq(0))
    with ctx.workprec(512):
        direct=arb(finite)+arb(0,arb(radius).upper())
        exact=arb(form['A_zeta'])*arb(s).zeta()+arb(form['B_constant'])
        assert direct.overlaps(exact)
        # The exact coefficient identity above, not overlap alone, identifies the sum.
        disjoint_zero=bool(direct.lower()>0 or direct.upper()<0)
        return dict(s=s,n=n,m=m,T=T,polynomial_identity=True,
                    derivative_method='truncated direct product and quotient, exact rationals',
                    finite_sum=[str(finite.numer()),str(finite.denom())],
                    rigorous_tail_radius=[str(radius.numer()),str(radius.denom())],
                    direct_sum_interval=interval(direct),raw_linear_interval=interval(exact),
                    intervals_overlap=True,direct_sum_excludes_zero=disjoint_zero,
                    seconds=time.monotonic()-start)


def gcd_formula_audit():
    # Independent of the arithmetic agent's factorial-floor implementation.
    primes=[p for p in range(2,151) if all(p%d for d in range(2,math.isqrt(p)+1))]
    count=0
    cases=0
    for n in range(2,121,2):
        for m in range((3*n+1)//14+1):
            common=math.gcd(*(math.comb(n,j)**3*math.comb(j+m,m)**7
                              *math.comb(n-j+m,m)**7 for j in range(n+1)))
            for p in primes:
                if p>n+m or p*p<=n+m:
                    continue
                a=common
                actual=0
                while a%p==0:
                    a//=p
                    actual+=1
                predicted=7*int(n%p+2*(m%p)>=2*p-1)
                assert actual==predicted,(n,m,p,actual,predicted)
                count+=1
            cases+=1
    return dict(n_even_max=120,parameter_pairs=cases,prime_checks=count,
                all_m_including_zero=True,large_prime_formula_verified=True)


def improved_integerization_audit():
    rows=[]
    for n in (56,112,224):
        for step in range(7):
            m=step*n//28
            form=exact_form(9,n,m)
            d=math.lcm(*range(1,n+1))
            G=form['G']
            assert all((fmpq(d,G)*v).denom()==1 for v in form['c2'])
            assert all((fmpq(d*d,G)*v).denom()==1 for v in form['c1'])
            sharp=fmpq(d**9,G)
            assert (sharp*form['A_zeta']).denom()==1
            assert (sharp*form['B_constant']).denom()==1
            gap=sharp/form['primitive_multiplier']
            assert gap.denom()==1 and gap>=1
            rows.append(dict(n=n,m=m,pole_rows_checked=n+1,
                             all_pole_coefficients_integral=True,
                             improved_to_primitive_integer=str(gap.numer())))
    return rows


def main():
    result=dict(gram=gram_audit(),linear_direct_sum=[direct_sum_audit(n,m,T=4096 if n==10 else 256)
                for n,m in ((2,0),(6,1),(10,2))],gcd_formula=gcd_formula_audit(),
                improved_integerization=improved_integerization_audit())
    (OUT/'independent-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(gram_count=len(result['gram']),linear=[{k:r[k] for k in
                    ('n','m','T','direct_sum_excludes_zero','seconds')} for r in result['linear_direct_sum']],
                    gcd_formula=result['gcd_formula'],
                    improved_integerization_cases=len(result['improved_integerization']))))


if __name__=='__main__':
    main()
