"""Finite index audit using exact coefficients of prime logarithms, not a proof."""
from fractions import Fraction as Q
from math import comb

def harmonic(n):
    return sum((Q(1,k) for k in range(1,n+1)), Q(0))

def addlog(out, a, c):
    p=2
    while p*p <= a:
        while a%p == 0:
            out[p]=out.get(p,Q(0))+c
            a//=p
        p+=1
    if a>1:
        out[a]=out.get(a,Q(0))+c

def moment_formula(n,N):
    out={0:Q(0)}
    for i in range(n+1):
        for j in range(n+1):
            c=Q((-1)**(i+j)*comb(n,i)*comb(n,j))
            for v in range(N):
                a,b=n+i+v+1,n+j+v+1
                if a==b:
                    out[0]+=c/a
                else:
                    addlog(out,b,c/(b-a))
                    addlog(out,a,-c/(b-a))
    return {k:v for k,v in out.items() if v}

def cutoff_formula(n,N):
    out={0:comb(2*n,n)*harmonic(N)}
    addlog(out,N,Q(-comb(2*n,n)))
    for k in range(1,n+1):
        for i in range(min(k-1,n-k)+1):
            for j in range(i+1,n-i+1):
                addlog(out,n+k,Q(2*comb(n,i)**2,j))
    for i in range(n+1):
        out[0]-=comb(n,i)**2*harmonic(n+i)
        out[0]+=comb(n,i)**2*(harmonic(N+n+i)-harmonic(N))
        for j in range(i+1,n+1):
            c=Q(2*(-1)**(i+j)*comb(n,i)*comb(n,j),j-i)
            for k in range(1,j-i+1):
                addlog(out,N+n+i+k,c)
                addlog(out,N,-c)
    return {k:v for k,v in out.items() if v}

for n in range(1,9):
    for N in range(1,9):
        assert moment_formula(n,N)==cutoff_formula(n,N),(n,N)
print('64 exact coefficient comparisons passed (1 <= n,N <= 8).')
