"""Finite all-prime certificates for the dense-zero shift construction.

No final coefficient gcd is used to construct the certificates. Exact Fraction
checks compare them to externally computed PF coefficients and primitive scale.
Default output is stdout; old-round files and source artifacts are read-only.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from functools import reduce
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)


def validate(D, n, m):
    if D not in (6, 8) or n < 2 or n % 2 or m < 0:
        raise ValueError("require D=6 or 8, even n>=2, and m>=0")
    if 2 * D * m > (10 - D) * n + 7:
        raise ValueError("outside properness domain")
    assert m <= n // 2


def primes_up_to(n):
    flags = bytearray(b"\1") * (n + 1)
    flags[:2] = b"\0\0"
    for p in range(2, math.isqrt(n) + 1):
        if flags[p]:
            flags[p*p:n+1:p] = b"\0" * ((n-p*p)//p+1)
    return [p for p in range(2, n+1) if flags[p]]


def vp_int(n, p):
    n = abs(n)
    if not n:
        raise ValueError("use a separate zero test for v_p(0)")
    answer = 0
    while n % p == 0:
        n //= p
        answer += 1
    return answer


def vp_rat(x, p):
    x = Fraction(x)
    return vp_int(x.numerator, p) - vp_int(x.denominator, p)


def vp_fact(n, p):
    answer = 0
    while n:
        n //= p
        answer += n
    return answer


def level(n, p):
    answer = 0
    while n >= p:
        n //= p
        answer += 1
    return answer


def lcm_to(n):
    return math.prod(p ** level(n, p) for p in primes_up_to(n))


def highest(D, n, m):
    validate(D, n, m)
    F = Fraction(math.factorial(n) ** (10-D), math.factorial(m) ** (2*D))
    power = D ** (D*(n+2*m))
    return [F * Fraction(math.factorial(D*(j+m)) * math.factorial(D*(n+m-j)),
                         power * math.factorial(j)**10 * math.factorial(n-j)**10)
            for j in range(n+1)]


def top_valuation(D, n, m, j, p):
    return ((10-D)*vp_fact(n,p)-2*D*vp_fact(m,p)
            +vp_fact(D*(j+m),p)+vp_fact(D*(n+m-j),p)
            -10*vp_fact(j,p)-10*vp_fact(n-j,p)-D*(n+2*m)*vp_int(D,p))


def fractional_prime_power(p, exponent):
    return Fraction(p**exponent) if exponent >= 0 else Fraction(1,p**(-exponent))


def finite_certificate(D, n, m):
    validate(D, n, m)
    C = highest(D, n, m)
    H, J = lcm_to(D*(n+m))//D, lcm_to(D*n)//D
    local = refined = Fraction(1)
    rows = []
    for p in primes_up_to(D*(n+m)):
        h, j0, e = level(D*(n+m),p)-vp_int(D,p), level(D*n,p)-vp_int(D,p), level(n,p)
        nu = min(top_valuation(D,n,m,j,p) for j in range(n+1))
        assert nu == min(vp_rat(c,p) for c in C)
        large = None
        if p*p>D*(n+m):
            r,s=n%p,m%p
            large=min((D*(u+s))//p+(D*(r-u+s))//p for u in range(r+1))
            assert large == nu
        exponent = 8*h+j0-nu
        if D%p:
            improved=max(s*j0-max(nu-(9-s)*h,-(9-s)*e) for s in range(1,10))
        else:
            improved=exponent
        assert improved <= exponent
        local *= fractional_prime_power(p,exponent)
        refined *= fractional_prime_power(p,improved)
        rows.append({"prime":p,"nu":nu,"h":h,"j0":j0,"e":e,
                     "local_exponent":exponent,"refined_exponent":improved,
                     "large_prime_floor_min":large})
    return {"D":D,"n":n,"m":m,"H":H,"J":J,"highest":C,
            "certificates":{"elementary":Fraction(D**(D*(n+2*m))*H**8*J),
                            "local":local,"refined":refined},"prime_bounds":rows}


def tail_certificate(D,n):
    """Round-2 p=9,m=n function, sums starting at k=n, shifts a/D."""
    if D not in (6,8) or n<2 or n%2:
        raise ValueError("require D=6 or 8 and even n>=2")
    E=lcm_to(2*D*n)//D
    assert E%lcm_to(n)==0
    return Fraction(E**9)


def primitive_multiplier(vector):
    vector=list(map(Fraction,vector))
    denominator=reduce(math.lcm,(a.denominator for a in vector),1)
    content=abs(reduce(math.gcd,(int(denominator*a) for a in vector)))
    if not content:
        raise ValueError("zero vector has no primitive multiplier")
    return Fraction(denominator,content)


def parse_pair(pair):
    return Fraction(int(pair[0]),int(pair[1]))


def audit_artifact(path):
    raw=path.read_bytes()
    data=json.loads(gzip.decompress(raw).decode("utf-8"))
    D,n,m=data["D"],data["n"],data["m"]
    cert=finite_certificate(D,n,m)
    poles=[[parse_pair(x) for x in row] for row in data["pole_coefficients_j_by_s1_to9"]]
    rho=list(map(parse_pair,data["rho_s1_to9"]))
    constants=list(map(parse_pair,data["B_a_a1_toD"]))
    final=list(map(parse_pair,data["raw_A_B"]))
    assert [row[8] for row in poles]==cert["highest"]
    assert all(c>0 for c in cert["highest"])
    for s in range(1,10):
        assert rho[s-1]==sum(row[s-1] for row in poles)
        for j in range(n+1):
            assert poles[n-j][s-1]==(-1)**(s+1)*poles[j][s-1]
    assert rho[0]==0 and all(rho[s-1]==0 for s in (2,4,6,8))
    divisors=[d for d in range(1,D+1) if D%d==0]
    weights=[-7776,1701,-224,1] if D==6 else [-32768,5376,-168,1]
    for s in (3,5,7):
        assert sum(w*d**s for w,d in zip(weights,divisors))==0
    kappa=sum(w*d**9 for w,d in zip(weights,divisors))
    assert final[0]==kappa*rho[8]>0
    assert final[1]==sum(w*sum(constants[a*D//d-1] for a in range(1,d+1))
                         for w,d in zip(weights,divisors))
    for prime_row in cert["prime_bounds"]:
        p,nu,h,e=map(prime_row.get,("prime","nu","h","e"))
        for row in poles:
            for s,c in enumerate(row,1):
                if not c: continue
                valuation=vp_rat(c,p)
                assert valuation>=nu-(9-s)*h
                if D%p:
                    assert valuation>=-(9-s)*e
    primitive=primitive_multiplier(final)
    assert primitive==parse_pair(data["primitive_multiplier"])
    audits={}
    for label,T in cert["certificates"].items():
        assert all((T*a).denominator==1 for a in [*rho,*constants,*final])
        ratio=T/primitive
        assert ratio.denominator==1 and ratio>0
        audits[label]={"multiplier":T,"ratio_to_primitive":ratio,
                       "log_multiplier_per_n":(math.log(T.numerator)-math.log(T.denominator))/n,
                       "log_gap_per_n":math.log(ratio.numerator)/n}
    return {"artifact":str(path),"artifact_sha256":hashlib.sha256(raw).hexdigest(),
            "D":D,"n":n,"m":m,"passed":True,"primitive_multiplier":primitive,
            "certificates":audits,"prime_bounds":cert["prime_bounds"]}


def audit_tail_artifact(path):
    raw=path.read_bytes()
    data=json.loads(gzip.decompress(raw).decode("utf-8"))
    D,n,m=data["D"],data["n"],data["m"]
    assert m==n and data["tail_start_k"]==n
    poles=[[parse_pair(x) for x in row] for row in data["pole_coefficients_j_by_s1_to9"]]
    rho=list(map(parse_pair,data["rho_s1_to9"]))
    constants=list(map(parse_pair,data["B_a_a1_toD"]))
    final=list(map(parse_pair,data["raw_A_B"]))
    E=lcm_to(n)
    for j,row in enumerate(poles):
        expected=(-1)**j*math.comb(n,j)**9*math.comb(n+j,n)*math.comb(2*n-j,n)
        assert row[8]==expected
        for s,c in enumerate(row,1):
            assert (E**(9-s)*c).denominator==1
    assert rho[0]==0 and all(rho[s-1]==0 for s in (2,4,6,8))
    for s in range(9):
        assert rho[s]==sum(row[s] for row in poles)
    T=tail_certificate(D,n)
    assert all((T*x).denominator==1 for x in [*rho,*constants,*final])
    primitive=primitive_multiplier(final)
    assert primitive==parse_pair(data["primitive_multiplier"])
    ratio=T/primitive
    assert ratio.denominator==1 and ratio>0
    return {"artifact":str(path),"artifact_sha256":hashlib.sha256(raw).hexdigest(),
            "D":D,"n":n,"m":m,"passed":True,"multiplier":T,
            "primitive_multiplier":primitive,"ratio_to_primitive":ratio,
            "log_multiplier_per_n":math.log(T.numerator)/n,
            "log_gap_per_n":math.log(ratio.numerator)/n}


def self_test():
    count=0
    for D in (6,8):
        for n in (2,4,6,8,10,12):
            for m in range(((10-D)*n+7)//(2*D)+1):
                finite_certificate(D,n,m)
                count+=1
    return {"all_prime_and_large_prime_cases":count,"passed":True}


def json_ready(value):
    if isinstance(value,Fraction): return [str(value.numerator),str(value.denominator)]
    if isinstance(value,int): return str(value) if abs(value)>2**53 else value
    if isinstance(value,dict): return {k:json_ready(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)): return [json_ready(v) for v in value]
    return value


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--D",type=int)
    parser.add_argument("--n",type=int)
    parser.add_argument("--m",type=int)
    parser.add_argument("--audit-index",type=Path)
    parser.add_argument("--tail-index",type=Path)
    parser.add_argument("--self-test",action="store_true")
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    if args.self_test:
        answer=self_test()
    elif args.audit_index:
        raw=args.audit_index.read_bytes()
        rows=[json.loads(line) for line in raw.decode("utf-8").splitlines() if line.strip()]
        cases=[audit_artifact(Path(row["artifact"])) for row in rows if row.get("status")=="ok"]
        assert len(cases)==len(rows)
        answer={"status":"passed","atom_count":len(cases),"index_path":str(args.audit_index),
                "index_sha256":hashlib.sha256(raw).hexdigest(),
                "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                "self_test":self_test(),"logs_are_floating_diagnostics":True,"cases":cases}
        if args.tail_index:
            tail_raw=args.tail_index.read_bytes()
            tail_rows=[json.loads(line) for line in tail_raw.decode("utf-8").splitlines() if line.strip()]
            tail_cases=[audit_tail_artifact(Path(row["artifact"])) for row in tail_rows]
            answer.update({"tail_count":len(tail_cases),"tail_index_path":str(args.tail_index),
                           "tail_index_sha256":hashlib.sha256(tail_raw).hexdigest(),"tail_cases":tail_cases})
    else:
        if None in (args.D,args.n,args.m): parser.error("supply --D --n --m, or --audit-index, or --self-test")
        answer=finite_certificate(args.D,args.n,args.m)
    rendered=json.dumps(json_ready(answer),ensure_ascii=False,indent=2)
    if args.output:
        args.output.write_text(rendered+"\n",encoding="utf-8")
        print(json.dumps({"output":str(args.output),"status":answer.get("status"),"atom_count":answer.get("atom_count"),"tail_count":answer.get("tail_count"),"self_test":answer.get("self_test")}))
    else:
        print(rendered)


if __name__=="__main__": main()
