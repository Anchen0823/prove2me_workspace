"""Independently re-audit every saved shift form from its full rational PF data."""
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
from flint import arb,ctx,fmpq,fmpz  # type: ignore

VERIFY=ROOT/"missions/zeta9/round3/verification"
INDEX=VERIFY/"shift-results.jsonl"
REPORT=VERIFY/"shift-audit.json"


def q(pair:list[str]) -> fmpq:
    return fmpq(int(pair[0]),int(pair[1]))


def direct_pf_check(D:int,n:int,m:int,F:fmpq,ell:list[int],poles:list[list[fmpq]]) -> None:
    for t in (fmpq(1,2),fmpq(m+1),fmpq(n+m+2)):
        direct=F*math.prod((t+fmpq(e,D) for e in ell),start=fmpq(1))
        direct/=math.prod(((t+j)**9 for j in range(n+1)),start=fmpq(1))
        pf=sum((poles[j][s-1]/(t+j)**s
                for j in range(n+1) for s in range(1,10)),fmpq(0))
        if direct!=pf:
            raise AssertionError("Stored PF coefficients do not match R(t)")


def audit_one(index_row:dict) -> dict:
    path=ROOT/index_row["artifact"]
    with gzip.open(path,"rt",encoding="utf-8") as stream:
        data=json.load(stream)
    D,n,m=data["D"],data["n"],data["m"]
    assert data["case_id"]==index_row["case_id"]
    ell=data["retained_ell"]
    assert ell==[e for e in range(-D*m,D*(n+m)+1)
                if not (e%D==0 and 0<=e//D<=n)]
    F=q(data["F"])
    assert F==fmpq(math.factorial(n)**(10-D),math.factorial(m)**(2*D))
    poles=[[q(v) for v in row] for row in data["pole_coefficients_j_by_s1_to9"]]
    assert len(poles)==n+1 and all(len(row)==9 for row in poles)
    direct_pf_check(D,n,m,F,ell,poles)
    rho=[sum((poles[j][s-1] for j in range(n+1)),fmpq(0))
         for s in range(1,10)]
    assert rho==[q(v) for v in data["rho_s1_to9"]]
    assert all(rho[s-1]==0 for s in (1,2,4,6,8)) and rho[8]>0
    assert all(poles[n-j][s-1]==(-1)**(s+1)*poles[j][s-1]
               for j in range(n+1) for s in range(1,10))

    constants=[]
    for a in range(1,D+1):
        value=-sum((poles[j][s-1]*sum((fmpq(D,D*k+a)**s
                                            for k in range(j)),fmpq(0))
                     for j in range(n+1) for s in range(1,10)),fmpq(0))
        constants.append(value)
    assert constants==[q(v) for v in data["B_a_a1_toD"]]
    divisors=data["divisors"]
    assert divisors==[d for d in range(1,D+1) if D%d==0]
    weights=data["weights"]
    assert math.gcd(*weights)==1 and weights[-1]>0
    assert all(sum(w*d**s for w,d in zip(weights,divisors))==0
               for s in (3,5,7))
    kappa=sum(w*d**9 for w,d in zip(weights,divisors))
    assert kappa==data["kappa9"] and kappa>0
    B_d=[sum((constants[a*D//d-1] for a in range(1,d+1)),fmpq(0))
         for d in divisors]
    assert B_d==[q(v) for v in data["B_d"]]
    A=rho[8]*kappa
    B=sum((w*v for w,v in zip(weights,B_d)),fmpq(0))
    assert [A,B]==[q(v) for v in data["raw_A_B"]]
    denominator=math.lcm(int(A.denom()),int(B.denom()))
    pre=[int((A*denominator).numer()),int((B*denominator).numer())]
    content=math.gcd(*pre)
    pair=[v//content for v in pre]
    multiplier=fmpq(denominator,content)
    assert denominator==int(data["raw_denominator"])
    assert pre==[int(v) for v in data["preprimitive_A_B"]]
    assert content==int(data["content"])
    assert pair==[int(v) for v in data["primitive_A_B"]]
    assert multiplier==q(data["primitive_multiplier"])
    assert [multiplier*A,multiplier*B]==[fmpq(v) for v in pair]
    digest=hashlib.sha256(",".join(map(str,pair)).encode()).hexdigest()
    assert digest==data["primitive_sha256"]==index_row["primitive_sha256"]
    assert hashlib.sha256((ROOT/"missions/zeta9/round3/scripts/shift_forms.py").read_bytes()).hexdigest()==data["script_sha256"]

    bits=max(abs(v).bit_length() for v in pair)+600
    with ctx.workprec(bits):
        z=arb(9).zeta()
        value=arb(fmpz(pair[1]))+arb(fmpz(pair[0]))*z
        sign=1 if value.lower()>0 else (-1 if value.upper()<0 else 0)
        assert sign==data["arb"]["sign"]==index_row["sign"]
        assert value.rel_accuracy_bits()>=80
        log_primitive=(value if sign>0 else -value).log()
        assert bool(log_primitive.lower()>0)==data["arb"]["above_one"]
        assert bool(log_primitive.upper()<0)==data["arb"]["below_one"]
        raw_value=value/arb(multiplier)
        assert (raw_value.lower()>0 if sign>0 else raw_value.upper()<0)
        raw_log=(raw_value if sign>0 else -raw_value).log()
        multiplier_log=arb(multiplier).log()
        assert abs(float(log_primitive)-index_row["log_abs"])<1e-8
        assert (raw_log+multiplier_log).overlaps(log_primitive)
        raw_below_one=bool(raw_log.upper()<0)
        raw_above_one=bool(raw_log.lower()>0)
        return {"case_id":data["case_id"],"D":D,"n":n,"m":m,
                "sign":sign,"primitive_below_one":bool(log_primitive.upper()<0),
                "raw_below_one":raw_below_one,"raw_above_one":raw_above_one,
                "log_primitive_per_n":float(log_primitive)/n,
                "log_multiplier_per_n":float(multiplier_log)/n,
                "log_raw_per_n":float(raw_log)/n,
                "primitive_sha256":digest,
                "audited_pole_coefficients":(n+1)*9}


def main() -> None:
    rows=[json.loads(line) for line in INDEX.read_text(encoding="utf-8").splitlines()
          if line.strip()]
    latest={row["case_id"]:row for row in rows}
    results=[audit_one(row) for row in latest.values() if row["status"]=="ok"]
    results.sort(key=lambda row:(row["n"],row["D"],row["m"]))
    report={"status":"ok","records":len(results),
            "all_primitive_above_one":all(not row["primitive_below_one"] for row in results),
            "raw_below_one_count":sum(row["raw_below_one"] for row in results),
            "negative_count":sum(row["sign"]<0 for row in results),
            "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "rows":results}
    REPORT.write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps({k:report[k] for k in ("status","records",
                                            "all_primitive_above_one",
                                            "raw_below_one_count","negative_count")},
                     ensure_ascii=False))


if __name__=="__main__":
    main()
