"""Root-agent exact polynomial, direct-sum, and special integerization checks."""
from fractions import Fraction
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'tmp/zeta7/exact_packages'))
sys.path.insert(0,str(ROOT/'missions/zeta9/scripts'))
sys.set_int_max_str_digits(0)
from flint import arb,ctx,fmpq,fmpq_poly,fmpz
from odd_linear_form import exact_form
from general_poles import exact_vector,interval

OUT=ROOT/'missions/zeta9/round2/verification'


def mul(a,b,order):
    return [sum((a[i]*b[j-i] for i in range(max(0,j-len(b)+1),min(j,len(a)-1)+1)),fmpq(0))
            for j in range(min(order+1,len(a)+len(b)-1))]


def direct_coefficient(p,n,m,k):
    d=9-p
    b=10-p
    numerator=[fmpq(1)]
    denominator=[fmpq(1)]
    for shift in list(range(-m,0))+list(range(n+1,n+m+1)):
        numerator=mul(numerator,[fmpq(math.comb(b,i)*(k+shift)**(b-i))
                                 for i in range(min(d,b)+1)],d)
    for shift in range(n+1):
        denominator=mul(denominator,[fmpq(math.comb(p,i)*(k+shift)**(p-i))
                                     for i in range(min(d,p)+1)],d)
    numerator += [fmpq(0)]*(d+1-len(numerator))
    denominator += [fmpq(0)]*(d+1-len(denominator))
    quotient=[]
    for j in range(d+1):
        quotient.append((numerator[j]-sum((denominator[i]*quotient[j-i]
                                          for i in range(1,j+1)),fmpq(0)))/denominator[0])
    return quotient[d]*fmpq(math.factorial(n)**p,math.factorial(m)**(2*b))


def polynomial_identity(form):
    p,n,m=form['p'],form['n'],form['m']
    t=fmpq_poly([0,1])
    numerator=fmpq_poly([1])
    denominator=fmpq_poly([1])
    for shift in list(range(-m,0))+list(range(n+1,n+m+1)):
        numerator *= (t+shift)**(10-p)
    numerator *= fmpq(math.factorial(n)**p,math.factorial(m)**(2*(10-p)))
    for j in range(n+1):
        denominator *= (t+j)**p
    check=fmpq_poly([0])
    for order,cs in form['pole_coeffs'].items():
        for j,c in enumerate(cs):
            q,r=divmod(denominator,(t+j)**order)
            assert not r
            check += c*q
    assert check==numerator


def direct_check(p,n,m,T=1024):
    form=exact_vector(p,n,m)
    polynomial_identity(form)
    finite=sum((direct_coefficient(p,n,m,k) for k in range(1,T+1)),fmpq(0))
    d=form['d']
    if d:
        pf_radius=sum((abs(c)*math.comb(d+j-1,d)*fmpq(1,(d+j-1)*(T+k)**(d+j-1))
                    for j,cs in form['pole_coeffs'].items() for k,c in enumerate(cs)),fmpq(0))
        assert T>=2*(n+m)
        b=form['b']
        gamma=p*(n+1)+d-2*b*m
        # Cauchy circle |z-k|=k/2: each numerator factor <=2k, each
        # denominator factor >=k/2, and the d-th Taylor coefficient
        # has one additional factor (k/2)^(-d).
        cauchy_radius=fmpq(math.factorial(n)**p*2**(2*b*m+p*(n+1)+d),
                          math.factorial(m)**(2*b)*(gamma-1)*T**(gamma-1))
        radius=min(pf_radius,cauchy_radius)
        tail_method='minimum of absolute partial fractions and Cauchy product tail bounds'
    else:
        assert m==n and T>=n
        # R(k) <= n!^7 3^n k^(-7n-9), for k>=n.
        radius=fmpq(math.factorial(n)**7*3**n,(7*n+8)*T**(7*n+8))
        tail_method='positive rational-product bound and integral test'
    with ctx.workprec(512):
        raw=arb(form['raw_vector'][0])
        for order,c in zip(form['zeta_orders'],form['raw_vector'][1:]):
            raw+=arb(c)*arb(order).zeta()
        enclosing=arb(finite)+arb(0,arb(radius).upper())
        assert enclosing.overlaps(raw)
        excludes_zero=bool(enclosing.lower()>0 or enclosing.upper()<0)
        assert excludes_zero,(p,n,m,T)
        return dict(p=p,n=n,m=m,T=T,polynomial_identity=True,
                    tail_method=tail_method,
                    finite_sum=[str(finite.numer()),str(finite.denom())],
                    tail_radius=[str(radius.numer()),str(radius.denom())],
                    raw_zeta_interval=interval(raw),direct_sum_interval=interval(enclosing),
                    certified_nonzero=True)


def canonical_p9():
    rows=[]
    for n in (2,4,8,12,24,48):
        form=exact_vector(9,n,n)
        d=math.lcm(*range(1,n+1))
        assert all((d**(9-j)*c).denom()==1 for j,cs in form['pole_coeffs'].items() for c in cs)
        integers=[x*d**9 for x in form['raw_vector']]
        assert all(v.denom()==1 for v in integers)
        bits=max(512,int(3.6*max(len(str(v.numer())) for v in integers))+256)
        with ctx.workprec(bits):
            value=arb(integers[0])
            for order,c in zip(form['zeta_orders'],integers[1:]):
                value+=arb(c)*arb(order).zeta()
            assert value.lower()>0
            rows.append(dict(n=n,m=n,orders=form['zeta_orders'],
                             dn=str(d),integer_vector=[str(v.numer()) for v in integers],
                             positive=True,below_one=bool(value.upper()<1),
                             value_interval=interval(value),log_per_n=interval(value.log()/n)))
    return rows


def analytic_inequalities():
    difference=201**10-301*101**10
    assert difference==74387623546099706050700 and difference>0
    with ctx.workprec(256):
        assert arb(3).log().upper()<arb(fmpq(11,10)).lower()
        assert arb(2).log().lower()>arb(fmpq(69,100)).upper()
        assert arb(400).log().upper()<6
        maximum_bound=3*arb(3).log()-20*arb(2).log()+(1+arb(400).log())/100
        tail_bound=arb(fmpq(1,5))-7*arb(10).log()
        assert maximum_bound.upper()<arb(fmpq(-1043,100)).lower()
        assert tail_bound.upper()<-15
        return dict(integer_derivative_comparison=str(difference),
                    global_phase_bound=interval(maximum_bound),
                    tail_exponent_bound=interval(tail_bound),
                    proved_phase_upper='-10.43',proved_integer_form_upper='-1.43',
                    scope='positive multi-zeta form only')


def main():
    checks=[]
    for n,m in ((6,1),(12,2),(24,5)):
        old=exact_form(9,n,m)
        new=exact_vector(3,n,m)
        assert new['raw_vector']==[old['B_constant'],old['A_zeta']]
        assert new['primitive_vector']==list(reversed(old['primitive']))
        checks.append(dict(n=n,m=m,raw_and_primitive_equal=True))
    direct=[direct_check(p,n,m) for p,n,m in ((3,6,1),(5,4,1),(7,4,1),(9,4,4))]
    special=canonical_p9()
    OUT.mkdir(parents=True,exist_ok=True)
    result=dict(p3_regression=checks,direct_sum=direct,canonical_p9=special,
                analytic_inequalities=analytic_inequalities(),
                warning='Canonical p9 forms contain zeta3,zeta5,zeta7,zeta9; not a zeta9 proof.')
    (OUT/'independent-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(regressions=len(checks),direct_sums=len(direct),
                         special_p9=[dict(n=r['n'],below_one=r['below_one']) for r in special])))


if __name__=='__main__':
    main()
