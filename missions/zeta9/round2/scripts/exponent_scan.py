"""Exploratory real rates for the second-round odd-zeta rational functions.

The p=9 column is a positive-sum Laplace rate, not a single-zeta result.
The p<9 columns are half-integer vertical-contour upper rates only.
"""

from __future__ import annotations

import argparse
import math


def phase_real(p: int, a: float, x: float) -> float:
    b = 10-p
    assert x > a > 0
    return (-2*b*a*math.log(a) + 10*x*math.log(x)
            + b*(x+1+a)*math.log(x+1+a)
            - b*(x-a)*math.log(x-a)
            - 10*(x+1)*math.log(x+1))


def phase_prime_real(p: int, a: float, x: float) -> float:
    b = 10-p
    return (10*math.log(x/(x+1))
            + b*math.log((x+1+a)/(x-a)))


def positive_sum_peak_p9(a: float) -> tuple[float, float]:
    assert 0<a<4.5
    lo = a+1e-12
    hi = max(1., 2*a)
    while phase_prime_real(9,a,hi)>0:
        hi *= 2
    for _ in range(100):
        mid = (lo+hi)/2
        if phase_prime_real(9,a,mid)>0:
            lo = mid
        else:
            hi = mid
    peak = (lo+hi)/2
    return peak, phase_real(9,a,peak)


def vertical_prime(p: int,a:float,y:float)->float:
    b=10-p
    decay=2*math.pi if p<9 else 0.
    return (b*math.pi/2-decay-10*math.atan(y/a)
            -b*math.atan(y/(1+2*a))+10*math.atan(y/(1+a)))


def vertical_rate(p:int,a:float,y:float)->float:
    b=10-p
    return (-2*b*a*math.log(a)+5*a*math.log(a*a+y*y)
            +b*(1+2*a)/2*math.log((1+2*a)**2+y*y)
            -5*(1+a)*math.log((1+a)**2+y*y)
            +y*vertical_prime(p,a,y))


def vertical_peak(p:int,a:float)->tuple[float,float]:
    assert p in (3,5,7)
    if vertical_prime(p,a,0)<=0:
        return 0.,vertical_rate(p,a,0.)
    lo,hi=0.,1.
    while vertical_prime(p,a,hi)>0:
        hi*=2
    for _ in range(100):
        mid=(lo+hi)/2
        if vertical_prime(p,a,mid)>0:lo=mid
        else:hi=mid
    peak=(lo+hi)/2
    return peak,vertical_rate(p,a,peak)


def main()->None:
    parser=argparse.ArgumentParser()
    parser.add_argument("--p",type=int,choices=(3,5,7,9),default=9)
    args=parser.parse_args()
    p=args.p
    grid={3:[1/28,1/14,3/28,1/7,5/28,3/14],
          5:[1/4,2/5,1/2],
          7:[1/2,1,7/6],
          9:[1/2,1,3/2,2,3,4,9/2]}[p]
    for a in grid:
        if p==9 and a==4.5:
            print(f"p=9 alpha={a:g} supremum at infinity, rate={-9*math.log(a):.12g}")
        else:
            x,rate=(positive_sum_peak_p9(a) if p==9 else vertical_peak(p,a))
            print(f"p={p} alpha={a:g} peak={x:.12g} rate={rate:.12g}")


if __name__=="__main__":
    main()
