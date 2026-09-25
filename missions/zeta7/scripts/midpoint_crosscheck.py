"""Independent, vectorized numerical cross-check of proposed arithmetic formulas.

The local valuation lemmas must be proved separately. This midpoint quadrature
does NOT certify the integrals or any asymptotic theorem.
"""
import math
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tmp/zeta7/exact_packages'))
import numpy as np


def inner_R(x, alpha, q, s, lam=None):
    if lam is None: lam = 1-alpha
    H = lam+q*alpha
    f = np.mod(x, 1); g = np.mod(alpha*x, 1)
    df = np.minimum(f, 1-f); dg = np.minimum(g, 1-g)
    ef = np.where(f <= .5, 1, -1); eg = np.where(g <= .5, 1, -1)
    var = dg*(1-2*dg)
    cov = ef*eg*(np.minimum(df,dg)-2*df*dg)
    T = np.floor(2*H*x); u = H*x-T/2
    k = np.floor(2*x); np_ = (2*x-k)/2
    gamma = (.5*T*(T-2*x-s)-q*q*(2*alpha*alpha*x*x+var)
             + q*(alpha*x*(2*x+s)+cov)
             + u*(2*T-k-s)+np.maximum(u-np_,0))
    j = np.floor(2*lam*x)
    nscalar = 2*lam*x*np.floor(x)-4*q*lam*x*np.floor(alpha*x)-2*(j*lam*x-j*(j+1)/4)
    return -gamma-nscalar


def class_cost(ell, delta, q, s):
    cost = np.zeros_like(ell); z = np.zeros_like(ell)
    for i in range(8):
        exists = i < ell-delta
        w = np.where(i < ell-2, np.minimum(0,i+q*delta-(ell+s-1)/2),0)
        cost += np.where(exists,-2*w,0)
        z += exists & (w==0)
    return cost,z


def outer(y,alpha,q,s,lam=None):
    if lam is None: lam=1-alpha
    x=1/y; f=np.mod(x,1); d=np.minimum(f,1-f)
    e=np.where(f<=.5,1,-1)
    ell=np.rint(2*x-2*e*d)
    zcut=alpha*x
    if np.any(zcut>.5):
        raise ValueError('Need alpha < 1/6 for this outer formula')
    lengths=[np.minimum(d,zcut),np.maximum(zcut-d,0),np.maximum(d-zcut,0),.5-np.maximum(d,zcut)]
    c=np.zeros_like(x); z=np.zeros_like(x)
    for length,L,delta in zip(lengths,[ell+e,ell,ell+e,ell],[1,1,0,0]):
        cc,zz=class_cost(L,delta,q,s)
        c+=length*cc;z+=length*zz
    c=np.where(y<1,c*y,0)
    z=np.where(y<1,z*y+lam-(1-alpha),lam)
    r=np.maximum(2*lam-1+2*q*alpha-(s-1)/2*y,0)
    scalar=-2*lam*np.floor(x)
    for j in range(1,math.ceil(6*lam)+1): scalar+=np.maximum(2*lam-j*y,0)
    return c+np.minimum(r,z)+scalar


def assess_arith(alpha,q,s=7,M=400,points=200000,lam=None):
    if not 0<alpha<1/6:
        raise ValueError('This experiment only covers 0 < alpha < 1/6')
    # Equal-spaced x resolves the many floor-function discontinuities.
    if lam is None: lam=1-alpha
    if lam<1-alpha-1e-12: raise ValueError('Requires lam >= 1-alpha')
    x=3+(np.arange(points)+.5)*(M-3)/points
    inn=float(np.sum(inner_R(x,alpha,q,s,lam)/x**3)*(M-3)/points)
    hi=max(1,2*lam,(2*lam-1+2*q*alpha)*2/(s-1))
    y=1/3+(np.arange(points)+.5)*(hi-1/3)/points
    out=float(np.sum(outer(y,alpha,q,s,lam))*(hi-1/3)/points)
    small=(s+1)*lam/M
    return dict(A_numeric=inn+out+small,inner=inn,outer=out,small=small,
                alpha=alpha,q=q,s=s,M=M,points=points,lam=lam,certified=False)


if __name__=='__main__':
    import json
    print(json.dumps(assess_arith(.075,3,s=5),indent=2))
    print(json.dumps(assess_arith(.075,3,s=7),indent=2))
