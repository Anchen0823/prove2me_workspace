"""Exact small certificate for the limiting recurrence obstruction.

No new n, lattice search, zeta evaluation, or parameter fitting.
"""
import hashlib
import json
import math
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'tmp/zeta7/exact_packages'))
sys.set_int_max_str_digits(0)
from flint import fmpq,fmpq_mat

BASE=ROOT/'missions/zeta9/round8'
SOURCE=ROOT/'missions/zeta9/round7/verification/arithmetic-connection-symbolic.json'


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def q(pair):return fmpq(int(pair[0]),int(pair[1]))
def mat(rows):return fmpq_mat([[q(x) for x in row] for row in rows])


def gf2_remainder(a,b):
    while a and a.bit_length()>=b.bit_length():
        a^=b << (a.bit_length()-b.bit_length())
    return a


def primitive(poly):
    coeff=list(poly)
    D=math.lcm(*(int(x.denom()) for x in coeff))
    values=[int((x*D).numer()) for x in coeff]
    content=math.gcd(*values)
    values=[x//content for x in values]
    if values[-1]<0:values=[-x for x in values]
    return values


def main():
    data=json.loads(SOURCE.read_text())
    limit=data['homogeneous_limit']
    M=mat(limit['C_limit']);G=mat(limit['inverse_weighted_limit'])
    assert M*G==G*M==fmpq_mat([[int(i==j) for j in range(5)] for i in range(5)])
    f=primitive(M.charpoly());Q=primitive(G.charpoly())
    assert f==[-22235661,33339376907507494,82488337575256095,10120051241400,10336452,1]
    assert Q==[-1,-10336452,-10120051241400,-82488337575256095,-33339376907507494,22235661]
    # f mod 2 = x^5+x^2+1. A reducible quintic over F2 has a
    # factor of degree <=2; the only monic irreducible quadratic is x^2+x+1.
    f2=sum((x%2)<<i for i,x in enumerate(f))
    tests={str(divisor):gf2_remainder(f2,divisor) for divisor in [0b10,0b11,0b111]}
    assert f2==0b100101 and all(tests.values())
    assert tests=={'2':1,'3':1,'7':1}
    assert Q[-1]>0 and all(x<0 for x in Q[:-1])
    # An exact cyclic row provides a separate concrete implementation check.
    row=fmpq_mat([[1,0,0,0,0]]);rows=[]
    for k in range(5):
        rows.append([row[0,j] for j in range(5)])
        row=row*G
    krylov=fmpq_mat(rows)
    assert krylov.det()!=0
    # Cauchy root bound and the resultant lower bound for degree <=4.
    a=Q[-1];R=1+max(abs(x) for x in Q[:-1])
    reciprocal_constant=a**4*5**4*R**16
    frozen=[]
    for suffix in ['', 'round2','round3','round4','round5','round6','round7']:
        base=ROOT/'missions/zeta9'/suffix
        path=base/'verification/artifact-manifest.json'
        manifest=json.loads(path.read_text())
        for item in manifest:
            file=base/item['path']
            assert file.stat().st_size==item['bytes'] and sha(file)==item['sha256']
        frozen.append(dict(round=suffix or 'round1',files=len(manifest),manifest_sha256=sha(path)))
    result=dict(status='passed',scope='exact constant limiting matrix only; no conclusion about actual moving short vectors',
        source_sha256=sha(SOURCE),
        forward_charpoly=f,inverse_primitive_charpoly=Q,
        forward_reduction_mod_2='x^5+x^2+1',
        gf2_linear_and_quadratic_remainders=tests,
        irreducibility_argument='Degree 5 reducible implies factor of degree 1 or 2; x, x+1, x^2+x+1 all fail.',
        inverse_coefficients_one_positive_leading_all_other_negative=True,
        krylov_determinant=[str(krylov.det().numer()),str(krylov.det().denom())],
        cauchy_integer_root_bound=str(R),
        filter_lower_bound='abs(p(rho)) >= 1/(constant * H(p)^4), for nonzero integer p of degree <=4',
        reciprocal_lower_bound_constant=str(reciprocal_constant),
        fixed_block_proof='Unique largest-modulus positive root rho; degree Q(rho)=5; rho^m cannot be rational because its conjugates would have equal moduli. Tower law gives degree Q(rho^m)=5 for each m>=1.',
        frozen_rounds=frozen,previous_files_verified=sum(x['files'] for x in frozen),
        script_sha256=sha(Path(__file__)))
    out=BASE/'verification/limit-obstruction.json'
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='passed',mod2='x^5+x^2+1',remainders=tests,
                         prior_files=result['previous_files_verified'])),flush=True)


if __name__=='__main__':main()
