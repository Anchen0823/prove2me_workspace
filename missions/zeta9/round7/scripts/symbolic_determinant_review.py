"""Independent polynomial-identity proof by 111 exact evaluations.

Each determinant has degree at most 110: columns have weighted degrees
20+2r (five old/new columns) and 11+2a (ten H columns), and row u^k
subtracts 2k. Sum 320 - 210 = 110. Equality at 111 distinct integers
therefore proves the polynomial identities, independently of Bareiss.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'tmp/zeta7/exact_packages'))
sys.path.insert(0,str(ROOT/'missions/zeta9/round7/scripts'))
sys.set_int_max_str_digits(0)
from flint import fmpq_poly,fmpq_mat,fmpq
from connection_audit import invariant_coefficients,independent_columns

OUT=ROOT/'missions/zeta9/round7/verification'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pair(q):return [str(q.numer()),str(q.denom())]


def factor_polynomial(data):
    result=fmpq_poly([int(data['content'])])
    for row in data['factors']:
        result*=fmpq_poly([int(x) for x in row['coefficients']])**int(row['exponent'])
    return result


def systems(n):
    t=fmpq_poly([0,1]);u=t*(t+n);v=t*(t+n-1);vp=(t+1)*(t+n)
    H=[(t-n-1)*(t+n+1)**10*v**a-(t+2*n+1)*(t-1)**10*vp**a for a in range(10)]
    old=[(u-n-1)**10*u**r for r in range(5)]
    Z=fmpq_poly([1])
    for a in [1,2,3]:Z*=u-(n+a)*(2*n+a)
    new=[((n+1)*(n+2))**7*Z*(u-n-1)**r for r in range(5)]
    def mat(cols):
        rows=[invariant_coefficients(p,u) for p in cols]
        return fmpq_mat([[row[k] if k<len(row) else 0 for row in rows] for k in range(15)])
    return mat(old+H),mat(new+H)


def main():
    started=time.monotonic();source=OUT/'arithmetic-connection-symbolic.json'
    data=json.loads(source.read_text())
    old=factor_polynomial(data['old_system_determinant'])
    new=factor_polynomial(data['new_system_determinant'])
    assert old.degree()==new.degree()==110
    points=[]
    for n in range(2,224,2):
        assert time.monotonic()-started<120
        A,B=systems(n);da,db=A.det(),B.det()
        assert da==old(n) and db==new(n)
        points.append(dict(n=n,old_det=pair(da),new_det=pair(db)))
    assert len(points)==111
    x=fmpq_poly([0,1]);num=21*x*(3*x+2)*(3*x+4)
    for k in range(1,7):num*=7*x+2*k
    den=(x+2)**9
    assert new*den==old*num
    initial=fmpq_mat(independent_columns(2)).det()
    assert initial==2160
    finite=[]
    for n in [2,4,6,12,24,48,96,192]:
        h=n//2
        closed=fmpq(math.factorial(3*h)*math.factorial(7*h),14*h*math.factorial(h)**10)
        direct=fmpq_mat(independent_columns(n)).det()
        assert direct==closed
        finite.append(dict(n=n,determinant=pair(direct)))
    # Equality of closed forms under the connection step is algebraic;
    # the factorial quotient gives exactly the displayed rational ratio.
    result=dict(status='passed',source_sha256=sha(source),polynomial_degree_bound=110,
        degree_bound_argument='sum_r(20+2r)+sum_a(11+2a)-sum_k(2k)=110; n-degree of [u^k] column is at most its weighted degree minus 2k',
        exact_points=points,ratio_formula_verified_by_polynomial_multiplication=True,
        initial_det_F2='2160',finite_full_map_determinants=finite,
        determinant_closed_form='det F_(2h)=(3h)!(7h)!/(14h(h!)^10)',
        seconds=time.monotonic()-started,script_sha256=sha(Path(__file__)))
    (OUT/'symbolic-determinant-independent.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='passed',exact_points=len(points),degree_bound=110,full_map_checks=len(finite),seconds=result['seconds'])),flush=True)


if __name__=='__main__':main()
