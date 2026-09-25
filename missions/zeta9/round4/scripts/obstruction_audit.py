"""Independent read-only audit of the finite denominator obstruction artifacts."""
from __future__ import annotations

import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"tmp/zeta7/exact_packages"))
from flint import fmpq  # type: ignore
from prime_scan import WEIGHTS,coeffs,modular_contributions  # type: ignore

VERIFY=ROOT/"missions/zeta9/round4/verification"
TAIL=ROOT/"missions/zeta9/round3/verification"


def q(pair:list[str]) -> fmpq:
    return fmpq(int(pair[0]),int(pair[1]))


def interval(data:dict) -> tuple[fmpq,fmpq]:
    mid,rad,exp=int(data["mid"]),int(data["rad"]),int(data["exp"])
    factor=fmpq(10**exp) if exp>=0 else fmpq(1,10**(-exp))
    return fmpq(mid-rad)*factor,fmpq(mid+rad)*factor


def intersects(a:tuple[fmpq,fmpq],b:tuple[fmpq,fmpq]) -> bool:
    return a[0]<=b[1] and b[0]<=a[1]


def rational_R(n:int,t:fmpq) -> fmpq:
    F=fmpq(math.factorial(n)**7)
    numerator=math.prod(((t-j)*(t+n+j) for j in range(1,n+1)),start=fmpq(1))
    denominator=math.prod(((t+j)**9 for j in range(n+1)),start=fmpq(1))
    return F*numerator/denominator


def audit(D:int,n:int) -> dict:
    path=VERIFY/f"obstruction-D{D}-n{n}.json"
    row=json.loads(path.read_text(encoding="utf-8"))
    assert row["D"]==D and row["n"]==n and row["m"]==n
    source=ROOT/"missions/zeta9/round4/scripts/denominator_obstruction.py"
    assert hashlib.sha256(source.read_bytes()).hexdigest()==row["source_sha256"]
    C=coeffs(n)
    assert C==[int(x) for x in row["highest_coefficients"]]
    divisors,weights=WEIGHTS[D]
    kappa=sum(w*d**9 for d,w in zip(divisors,weights))
    A=kappa*sum(C)
    assert A==int(row["A"]) and A!=0
    assert (1 if A>0 else -1)==row["A_sign"]
    scan_path=VERIFY/f"prime-scan-D{D}-n{n}.json.gz"
    with gzip.open(scan_path,"rt",encoding="utf-8") as stream:
        scan=json.load(stream)
    scan_outer={r["p"]:r for r in scan["prime_records"]
                if r["band"]=="Dn_lt_p_le_2Dn"}
    assert len(row["local_primes"])==len(scan_outer)
    suffix=[0]*(n+2)
    for j in range(n,-1,-1):
        suffix[j]=suffix[j+1]+C[j]
    for record in row["local_primes"]:
        p=record["p"]
        j0=(p+D-1)//D-n
        simple=(-pow(D,9,p)*(suffix[j0]%p))%p
        detailed=modular_contributions(D,n,C,p)[1]
        assert record["j0"]==j0 and record["residue"]==simple==detailed
        assert scan_outer[p]["residue_mod_p"]==simple
        assert record["forced_denominator_order"]==(9 if simple else None)
    forced=[record["p"] for record in row["local_primes"] if record["residue"]]
    assert forced==row["forced_primes"]
    Q=math.prod(p**9 for p in forced)
    assert Q==int(row["Q"])
    assert len(forced)==row["forced_prime_count"]
    raw_interval=interval(row["raw"]["interval"])
    assert (raw_interval[0]>0 if row["raw"]["sign"]>0 else raw_interval[1]<0)
    raw_abs_lower=(raw_interval[0] if raw_interval[0]>0 else -raw_interval[1])
    exact_lower=fmpq(Q,abs(A))*raw_abs_lower
    assert exact_lower>1
    certificate_interval=interval(row["primitive_abs_lower_bound"])
    assert certificate_interval[0]>1
    assert intersects(certificate_interval,(exact_lower,
        fmpq(Q,abs(A))*(raw_interval[1] if raw_interval[0]>0 else -raw_interval[0])))
    T=row["raw"]["T"]
    assert T==4*n
    folded=[sum(w for d,w in zip(divisors,weights) if (a*d)%D==0)
            for a in range(1,D+1)]
    assert len(row["raw"]["shift_rows"])==D
    for a,shift in enumerate(row["raw"]["shift_rows"],1):
        assert shift["a"]==a and shift["weight"]==folded[a-1]
        x=fmpq(D*T+a,D)
        delta=7*n+9
        expected=(fmpq(math.factorial(n)**7)
                  *(1+fmpq(2*n)/x)**(2*n)
                  /((delta-1)*x**(delta-1)))
        assert expected==q(shift["tail_bound"])
    cross=None
    if n==24:
        for a in (1,D):
            t=fmpq(D*n+a,D)
            first=rational_R(n,t)
            # Independently verify the archived direct-summation first term
            # and the one-step ratio formula used for all later terms.
            num=(math.factorial(n)**7*D**(7*n+9)
                 *math.prod((D*n+a-D*j for j in range(1,n+1)))
                 *math.prod((D*n+a+D*(n+j) for j in range(1,n+1))))
            den=math.prod(((D*n+a+D*j)**9 for j in range(n+1)))
            assert first==fmpq(num,den)
            ratio=fmpq(t**10*(t+2*n+1),
                        (t-n)*(t+n+1)**10)
            assert rational_R(n,t+1)==first*ratio
        with gzip.open(TAIL/f"tail-shift-D{D}-n24-m24.json.gz","rt",encoding="utf-8") as stream:
            old=json.load(stream)
        primitive_interval=interval(old["arb"]["value_interval"])
        M=q(old["primitive_multiplier"])
        exact_form_interval=(primitive_interval[0]/M,primitive_interval[1]/M)
        assert intersects(raw_interval,exact_form_interval)
        cross={"exact_form_interval_overlap":True,
               "first_term_and_ratio_checked_at_shifts":[1,D],
               "exact_form_sha256":old["primitive_sha256"]}
    return {"case_id":f"D{D}-n{n}","D":D,"n":n,
            "forced_primes":len(forced),"available_outer_primes":len(scan_outer),
            "raw_sign":row["raw"]["sign"],
            "exact_lower_bound_greater_than_one":True,
            "n24_exact_form_crosscheck":cross,
            "artifact_sha256":hashlib.sha256(path.read_bytes()).hexdigest()}


def main() -> None:
    results=[audit(D,n) for n in (24,48,96,192,384) for D in (6,8)]
    report={"status":"ok","cases":len(results),
            "n24_crosschecks":sum(row["n24_exact_form_crosscheck"] is not None
                                   for row in results),
            "all_exact_rational_lower_bounds_gt_one":True,
            "tail_bound_argument":
                "For t>=T+a/D>n, R(t)<=n!^7(1+2n/t)^n/t^(7n+9)"
                "<=n!^7(1+2n/(T+a/D))^(2n)/t^(7n+9)."
                " Monotone integral comparison bounds the omitted k>=T+1 sum"
                " by n!^7(1+2n/x)^(2n)/((7n+8)x^(7n+8)), x=T+a/D.",
            "primitive_bound_argument":
                "A is a nonzero integer; if B=b/q in lowest terms and Q|q,"
                " primitive multiplier=q/gcd(A,b)>=Q/abs(A).",
            "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "rows":results}
    path=VERIFY/"obstruction-audit.json"
    path.write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps({"status":"ok","cases":len(results),
                      "n24_crosschecks":report["n24_crosschecks"]}))


if __name__=="__main__":
    main()
