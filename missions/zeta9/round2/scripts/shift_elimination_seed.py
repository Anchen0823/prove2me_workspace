"""Exact constant weights for a possible future rational-shift construction.

Only the elimination identity is certified. No rational function, arithmetic
bound, asymptotic equality or zeta9 proof is supplied by this script.
"""
from fractions import Fraction
import json
import math
from pathlib import Path


def main():
    ds=[1,2,3,6]
    xs=[d*d for d in ds]
    weights=[Fraction(1,d**3*math.prod(x-y for y in xs if y!=x)) for d,x in zip(ds,xs)]
    denominator=math.lcm(*(w.denominator for w in weights))
    integers=[int(w*denominator) for w in weights]
    common=math.gcd(*integers)
    integers=[v//common for v in integers]
    sums={s:sum(w*d**s for w,d in zip(integers,ds)) for s in (1,3,5,7,9)}
    assert all(sums[s]==0 for s in (3,5,7))
    assert sums[9]!=0 and sums[1]!=0
    output=dict(divisors=ds,weights=integers,power_sums=sums,
                conditional_input='S_d=B_d+sum(rho_s*d^s*zeta(s), s=3,5,7,9)',
                conditional_output='sum(weights[d]*B_d)+power_sum[9]*rho_9*zeta(9)',
                independent_of_n=True,
                literature_url='https://arxiv.org/html/1803.08905',
                literature_hypothesis='s>=3D; s=9,D=6 fails this hypothesis',
                proved_scope='algebraic weights only; construction and estimates remain unproved')
    target=Path(__file__).resolve().parents[1]/'verification/shift-seed.json'
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(output))


if __name__=='__main__':
    main()
