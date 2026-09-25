"""Certified large-prime residues for the p=9,m=n tail-shift construction.

This computes denominator evidence without forming the full constant B.
The exact-B audit reads the six frozen round-3 artifacts only for verification.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from functools import lru_cache
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)


def primes_up_to(n):
    sieve=bytearray(b"\1")*(n+1)
    sieve[:2]=b"\0\0"
    for p in range(2,math.isqrt(n)+1):
        if sieve[p]: sieve[p*p:n+1:p]=b"\0"*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if sieve[p]]


def is_prime(p):
    return p>=2 and all(p%d for d in range(2,math.isqrt(p)+1))


def validate(D,n,p,outer=False):
    if D not in (6,8) or n<2 or n%2:
        raise ValueError("require D=6 or 8, even n>=2")
    if not is_prime(p) or p<=2*n or D%p==0:
        raise ValueError("require prime p>2n with p not dividing D")
    if p*p<=2*D*n:
        raise ValueError("p^2 multiples occur: p^9 B need not be p-integral")
    if outer and not D*n<p<=2*D*n:
        raise ValueError("outer formula requires Dn < p <= 2Dn")


def weights(D):
    if D==6: return [(1,-7776),(2,1701),(3,-224),(6,1)]
    if D==8: return [(1,-32768),(2,5376),(4,-168),(8,1)]
    raise ValueError("D must be 6 or 8")


@lru_cache(maxsize=4)
def exact_highest(n):
    """Integer recurrence, independent of modular harmonic calculations."""
    if n<2 or n%2: raise ValueError("even n>=2 required")
    C=[math.comb(2*n,n)]
    for j in range(n):
        numerator=-C[-1]*(n-j)**10*(n+j+1)
        denominator=(j+1)**10*(2*n-j)
        q,r=divmod(numerator,denominator)
        assert r==0
        C.append(q)
    assert C==list(reversed(C))
    return tuple(C)


def modular_highest(n,p):
    """Independent field recurrence, using no large integer coefficients."""
    if p<=2*n: raise ValueError("require p>2n")
    inv=[0]*(2*n+1)
    inv[1]=1
    for a in range(2,2*n+1): inv[a]=(-(p//a)*inv[p%a])%p
    c0=1
    for a in range(1,n+1): c0=c0*(n+a)*inv[a]%p
    C=[c0]
    for j in range(n):
        C.append((-C[-1]*pow(n-j,10,p)*(n+j+1)*pow(inv[j+1],10,p)*inv[2*n-j])%p)
    return C


def suffix_sums(C,p):
    suffix=[0]*(len(C)+1)
    for j in range(len(C)-1,-1,-1): suffix[j]=(C[j]+suffix[j+1])%p
    return suffix


def residue(D,n,p):
    """Return p^9 B mod p, with exact assumptions checked."""
    validate(D,n,p)
    C=modular_highest(n,p)
    suffix=suffix_sums(C,p)
    terms=[]
    total=0
    for d,w in weights(D):
        for a in range(1,(2*d*n)//p+1):
            cutoff=max(0,(a*p+d-1)//d-n)
            contribution=(-w*pow(d,9,p)*pow(a,-9,p)*suffix[cutoff])%p
            total=(total+contribution)%p
            terms.append({"d":d,"multiple_index":a,"cutoff":cutoff,
                          "suffix_mod_p":suffix[cutoff],"contribution_mod_p":contribution})
    result={"D":D,"n":n,"p":p,"p9B_mod_p":total,
            "certified_vp_B":-9 if total else None,
            "zero_means":"v_p(B)>=-8" if not total else None,"terms":terms}
    if p>D*n:
        cutoff=(p+D-1)//D-n
        simple=(-pow(D,9,p)*suffix[cutoff])%p
        assert total==simple
        result.update({"outer":True,"cutoff":cutoff,"truncated_highest_mod_p":suffix[cutoff]})
    else:
        result["outer"]=False
    return result


def lift_general(D,n,p):
    """Independent exact-integer top coefficients, general lift modulo p^2."""
    validate(D,n,p)
    C=exact_highest(n)
    H=[0]
    for k in range(1,2*n+1): H.append((H[-1]+pow(k,-1,p))%p)
    C8=[(C[j]%p)*(10*H[j]-10*H[n-j]-H[n+j]+H[2*n-j])%p for j in range(n+1)]
    top_suffix=suffix_sums(C,p*p)
    c8_suffix=suffix_sums(C8,p)
    lifted=0
    for d,w in weights(D):
        for a in range(1,(2*d*n)//p+1):
            cutoff=max(0,(a*p+d-1)//d-n)
            lifted-=w*(pow(d,9,p*p)*pow(a,-9,p*p)*top_suffix[cutoff]
                       +p*pow(d,8,p)*pow(a,-8,p)*c8_suffix[cutoff])
    lifted%=p*p
    first=residue(D,n,p)
    assert lifted%p==first["p9B_mod_p"]
    order=-9 if lifted%p else (-8 if lifted else None)
    answer={"D":D,"n":n,"p":p,"outer":p>D*n,"p9B_mod_p2":lifted,
            "p8B_mod_p":lifted//p if lifted%p==0 else None,"certified_vp_B":order,
            "if_unresolved":"v_p(B)>=-7" if order is None else None}
    if p>D*n:
        cutoff=(p+D-1)//D-n
        answer.update({"cutoff":cutoff,"top_sum_mod_p2":top_suffix[cutoff],
                       "c8_sum_mod_p":c8_suffix[cutoff]})
    return answer


def lift_outer(D,n,p):
    validate(D,n,p,outer=True)
    return lift_general(D,n,p)


def vp_int(a,p):
    if not a: raise ValueError("v_p(0) needs separate handling")
    a=abs(a); v=0
    while a%p==0: a//=p; v+=1
    return v


def rational_mod(x,p):
    if math.gcd(x.denominator,p)!=1: raise ValueError("denominator is not invertible modulo the supplied modulus")
    return (x.numerator%p)*pow(x.denominator%p,-1,p)%p


def audit_index(path):
    raw=path.read_bytes()
    rows=[json.loads(x) for x in raw.decode("utf-8").splitlines() if x.strip()]
    cases=[]; comparisons=0
    for row in rows:
        source=Path(row["artifact"])
        compressed=source.read_bytes()
        data=json.loads(gzip.decompress(compressed).decode("utf-8"))
        D,n=data["D"],data["n"]
        assert data["m"]==n and data["tail_start_k"]==n
        A,B=[Fraction(int(a),int(b)) for a,b in data["raw_A_B"]]
        assert A.denominator==1
        kappa=sum(w*d**9 for d,w in weights(D))
        assert A==kappa*sum(exact_highest(n))
        primes=[]
        for p in primes_up_to(2*D*n):
            if p<=2*n or D%p==0: continue
            if p*p<=2*D*n: continue
            found=residue(D,n,p)
            exact=rational_mod(p**9*B,p)
            assert exact==found["p9B_mod_p"]
            assert modular_highest(n,p)==[c%p for c in exact_highest(n)]
            found["exact_p9B_mod_p"]=exact
            found["actual_vp_B"]=vp_int(B.numerator,p)-vp_int(B.denominator,p)
            if exact: assert found["actual_vp_B"]==-9
            lifted=lift_general(D,n,p)
            assert lifted["p9B_mod_p2"]==rational_mod(p**9*B,p*p)
            found["mod_p2_lift"]=lifted
            primes.append(found); comparisons+=1
        cases.append({"artifact":str(source),"artifact_sha256":hashlib.sha256(compressed).hexdigest(),
                      "D":D,"n":n,"passed":True,"primes":primes})
    exceptional=[]
    for D,n,p in [(6,384,3767),(8,384,5527),(8,48,173),(8,192,947)]:
        lifted=lift_general(D,n,p)
        assert residue(D,n,p)["p9B_mod_p"]==0
        assert lifted["certified_vp_B"]==-8
        exceptional.append(lifted)
    try: residue(8,2,5)
    except ValueError: small_boundary=True
    else: raise AssertionError("unhandled p^2 denominator boundary")
    return {"status":"passed","index_path":str(path),"index_sha256":hashlib.sha256(raw).hexdigest(),
            "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "artifact_count":len(cases),"exact_prime_comparisons":comparisons,
            "p_squared_boundary_rejected":small_boundary,"cases":cases,
            "independently_lifted_exceptions":exceptional}


def json_ready(x):
    if isinstance(x,int): return str(x) if abs(x)>2**53 else x
    if isinstance(x,dict): return {k:json_ready(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [json_ready(v) for v in x]
    return x


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--D",type=int); ap.add_argument("--n",type=int); ap.add_argument("--p",type=int)
    ap.add_argument("--lift",action="store_true")
    ap.add_argument("--audit-index",type=Path); ap.add_argument("--output",type=Path)
    args=ap.parse_args()
    if args.audit_index: answer=audit_index(args.audit_index)
    else:
        if None in (args.D,args.n,args.p): ap.error("supply --D --n --p, or --audit-index")
        answer=lift_general(args.D,args.n,args.p) if args.lift else residue(args.D,args.n,args.p)
    rendered=json.dumps(json_ready(answer),ensure_ascii=False,indent=2)
    if args.output:
        args.output.write_text(rendered+"\n",encoding="utf-8")
        print(json.dumps({"output":str(args.output),"status":answer.get("status"),
                          "artifact_count":answer.get("artifact_count"),
                          "exact_prime_comparisons":answer.get("exact_prime_comparisons")}))
    else: print(rendered)


if __name__=="__main__": main()
