"""Generalized Fauzan arithmetic constants (floating evaluation, not a certificate).

The local valuation formulas are proved in research/arithmetic.md.  Integration
exploits their piecewise affine shape, with an independent midpoint check.
The 2N<p outer-range construction is implemented for every h.  Extra rows
when h>K-N are polynomial multiples of D_tail.  When h<K-N, Cauchy--Binet
retains h most negative weights from the full pole basis.
"""
import argparse
import json
import math


def _floor(x):
    return math.floor(x + 1e-11)


def ell(x, z):
    return _floor(x - z) + _floor(x + z) + 1


def _z_breaks(x, alpha):
    out = [0.0, 0.5]
    for u in (x, alpha*x):
        f = u - math.floor(u)
        for v in (f, 1-f):
            if 1e-12 < v < .5-1e-12:
                out.append(v)
    return sorted(set(out))


def inner_R(x, alpha, q, s=7, lam=None):
    lam = 1-alpha if lam is None else lam
    H = lam + q*alpha
    T = _floor(2*H*x)
    u = H*x-T/2
    k = _floor(2*x)
    nplus = (2*x-k)/2
    gamma = 0.0
    zs = _z_breaks(x, alpha)
    for a,b in zip(zs,zs[1:]):
        z = (a+b)/2
        l = ell(x,z)
        bn = q*ell(alpha*x,z)
        L = T-bn
        if L < 0:
            raise ValueError(f'negative inner dimension: x={x}, L={L}')
        gamma += (b-a)*L*(T+bn-l-s)
    gamma += u*(2*T-k-s) + max(0,u-nplus)
    v = lam*x
    m = _floor(2*v)
    J = m*v-m*(m+1)/4
    scalar = 2*lam*x*_floor(x)-4*q*lam*x*_floor(alpha*x)-2*J
    return -gamma-scalar


def _points_from_slopes(slopes, lo, hi):
    out = [lo,hi]
    for c in slopes:
        c = abs(c)
        if c <= 1e-14:
            continue
        for k in range(math.floor(c*lo)+1, math.ceil(c*hi)):
            v = k/c
            if lo < v < hi:
                out.append(v)
    out.sort()
    unique = []
    for x in out:
        if not unique or x-unique[-1] > 1e-10:
            unique.append(x)
    return unique


def inner_integral(alpha, q, s=7, B=3, M=200, lam=None):
    lam = 1-alpha if lam is None else lam
    H = lam+q*alpha
    points = _points_from_slopes(
        [2,2*alpha,2*lam,2*H,2*(H-1),2*(1-alpha),2*(1+alpha)],B,M)
    total = 0.0
    error = 0.0
    for l,r in zip(points,points[1:]):
        x1 = (2*l+r)/3
        x2 = (l+2*r)/3
        f1 = inner_R(x1,alpha,q,s,lam)
        f2 = inner_R(x2,alpha,q,s,lam)
        a = (f2-f1)/(x2-x1)
        b = f1-a*x1
        fm = inner_R((l+r)/2,alpha,q,s,lam)
        error = max(error,abs(fm-(f1+f2)/2))
        # These factorizations avoid subtracting almost identical reciprocals.
        total += a*(r-l)/(l*r) + b*(r-l)*(r+l)/(2*l*l*r*r)
    return total, error, len(points)-1


def outer_components(y,alpha,q,s=7,lam=None):
    lam = 1-alpha if lam is None else lam
    x = 1/y
    cost = 0.0
    zeros = lam
    if y < 1:
        negative_density = {}
        zs = _z_breaks(x,alpha)
        for a,b in zip(zs,zs[1:]):
            z = (a+b)/2
            l = ell(x,z)
            delta = int(z < alpha/y)
            ws = [min(0,i+q*delta-(l+s-1)/2) if i < l-2 else 0
                  for i in range(l-delta)]
            for w in ws:
                if w < 0:
                    negative_density[w] = negative_density.get(w,0)+(b-a)*y
        remaining = lam
        for w,density in sorted(negative_density.items()):
            take = min(remaining,density)
            cost -= 2*w*take
            remaining -= take
            if remaining <= 0: break
        zeros = max(0,lam-sum(negative_density.values()))
    rank = max(0,2*lam-1+2*q*alpha-(s-1)*y/2)
    scalar = -2*lam*_floor(1/y)
    scalar += sum(max(0,2*lam-j*y) for j in range(1,_floor(2*lam/y)+1))
    return cost, zeros, rank, scalar


def outer_integral(alpha,q,s=7,B=3,lam=None):
    lam=1-alpha if lam is None else lam
    if not 0 < alpha < 1/(2*B):
        raise ValueError('Requires 0<alpha<1/(2B), so outer classes remove at most one pole')
    lo=1/B
    hi=max(1,2*lam,(2*lam-1+2*q*alpha)*2/(s-1))
    pts=[lo,hi,1]
    for c in [2,2*alpha,2*(1-alpha),2*(1+alpha),2*lam]:
        for k in range(1,math.ceil(c/lo)+1):
            y=c/k
            if lo < y < hi:
                pts.append(y)
    cutoff=(2*lam-1+2*q*alpha)*2/(s-1)
    if lo < cutoff < hi:
        pts.append(cutoff)
    pts=sorted(set(pts))
    # Truncation to the h most negative weights introduces further kinks.
    # Each cumulative density is affine between these base breakpoints.
    extra=[]
    for l,r in zip(pts,pts[1:]):
        if r-l < 1e-12 or l >= 1: continue
        cumulative=[]
        for y in ((2*l+r)/3,(l+2*r)/3):
            ds={}
            zs=_z_breaks(1/y,alpha)
            for a,b in zip(zs,zs[1:]):
                z=(a+b)/2; ll=ell(1/y,z); delta=int(z<alpha/y)
                for i in range(max(0,ll-2)):
                    w=min(0,i+q*delta-(ll+s-1)/2)
                    if w<0: ds[w]=ds.get(w,0)+(b-a)*y
            cumulative.append(ds)
        y1=(2*l+r)/3; y2=(l+2*r)/3
        d1=d2=0.
        for w in sorted(set(cumulative[0])|set(cumulative[1])):
            d1+=cumulative[0].get(w,0); d2+=cumulative[1].get(w,0)
            slope=(d2-d1)/(y2-y1)
            if abs(slope)>1e-10:
                root=y1+(lam-d1)/slope
                if l+1e-10<root<r-1e-10: extra.append(root)
    pts=sorted(set(pts+extra))
    roots=[]
    for l,r in zip(pts,pts[1:]):
        if r-l<1e-12: continue
        y1=(2*l+r)/3; y2=(l+2*r)/3
        c1,z1,r1,n1=outer_components(y1,alpha,q,s,lam)
        c2,z2,r2,n2=outer_components(y2,alpha,q,s,lam)
        a=((z2-r2)-(z1-r1))/(y2-y1)
        b=(z1-r1)-a*y1
        if abs(a)>1e-10:
            root=-b/a
            if l+1e-10<root<r-1e-10: roots.append(root)
    pts=sorted(set(pts+roots))
    total=err=0.0
    residue_total=rank_total=scalar_total=0.0
    for l,r in zip(pts,pts[1:]):
        if r-l<1e-12: continue
        vals=[]
        for y in ((2*l+r)/3,(l+2*r)/3,(l+r)/2):
            c,z,rank,n=outer_components(y,alpha,q,s,lam)
            vals.append(c+min(z,rank)+n)
        err=max(err,abs(vals[2]-(vals[0]+vals[1])/2))
        total+=(r-l)*vals[2]
        c,z,rank,n=outer_components((l+r)/2,alpha,q,s,lam)
        residue_total+=(r-l)*c
        rank_total+=(r-l)*min(z,rank)
        scalar_total+=(r-l)*n
    return total,err,dict(residues=residue_total,rank=rank_total,scalar=scalar_total)


def arithmetic(alpha,q,s=7,B=3,M=200,lam=None):
    lam=1-alpha if lam is None else lam
    if not B > 1 or not M > B:
        raise ValueError('Requires 1<B<M')
    allocation_margin=min(2*(lam+q*alpha)*B-q,lam/alpha-q)
    if allocation_margin <= 0:
        raise ValueError('Inner allocation has no positive uniform margin')
    outer,outer_error,parts=outer_integral(alpha,q,s,B,lam)
    inner,inner_error,pieces=inner_integral(alpha,q,s,B,M,lam)
    small=(s+1)*lam/M
    return dict(s=s,alpha=alpha,q=q,lam=lam,B=B,M=M,arithmetic=outer+inner+small,
                outer=outer,inner=inner,small=small,outer_parts=parts,
                affine_check=max(outer_error,inner_error),inner_pieces=pieces,
                allocation_margin=allocation_margin)


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--s',type=int,default=7)
    p.add_argument('--alpha',type=float,default=.075)
    p.add_argument('--q',type=int,default=4)
    p.add_argument('--B',type=float,default=3)
    p.add_argument('--M',type=int,default=200)
    p.add_argument('--lam',type=float)
    args=p.parse_args()
    print(json.dumps(arithmetic(**vars(args)),indent=2))
