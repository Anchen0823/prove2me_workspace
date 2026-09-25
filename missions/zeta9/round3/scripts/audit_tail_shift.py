"""Read-only exact and Arb audit of the six archived tail-shift forms."""
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


def q(pair:list[str]) -> fmpq:
    return fmpq(int(pair[0]),int(pair[1]))


def audit(row:dict) -> dict:
    with gzip.open(ROOT/row["artifact"],"rt",encoding="utf-8") as stream:
        a=json.load(stream)
    D,n,m=a["D"],a["n"],a["m"]
    assert m==n and a["tail_start_k"]==m
    F=q(a["F"])
    assert F==fmpq(math.factorial(n)**9,math.factorial(n)**2)
    poles=[[q(v) for v in line] for line in a["pole_coefficients_j_by_s1_to9"]]
    assert len(poles)==n+1 and all(len(line)==9 for line in poles)
    for shift in (1,D):
        t=fmpq(m*D+shift,D)
        direct=F*math.prod((t-r for r in range(1,m+1)),start=fmpq(1))
        direct*=math.prod((t+n+r for r in range(1,m+1)),start=fmpq(1))
        direct/=math.prod(((t+j)**9 for j in range(n+1)),start=fmpq(1))
        pf=sum((poles[j][s-1]/(t+j)**s for j in range(n+1)
                for s in range(1,10)),fmpq(0))
        assert direct==pf and direct>0
    rho=[sum((poles[j][s-1] for j in range(n+1)),fmpq(0))
         for s in range(1,10)]
    assert rho==[q(v) for v in a["rho_s1_to9"]]
    assert all(rho[s-1]==0 for s in (1,2,4,6,8))
    assert all(poles[n-j][s-1]==(-1)**(s+1)*poles[j][s-1]
               for j in range(n+1) for s in range(1,10))
    constants=[]
    for shift in range(1,D+1):
        value=-sum((poles[j][s-1]
                    *sum((fmpq(D,D*k+shift)**s for k in range(j+m)),fmpq(0))
                    for j in range(n+1) for s in range(1,10)),fmpq(0))
        constants.append(value)
    assert constants==[q(v) for v in a["B_a_a1_toD"]]
    divisors=a["divisors"]
    weights=a["weights"]
    assert divisors==[d for d in range(1,D+1) if D%d==0]
    assert math.gcd(*weights)==1 and weights[-1]>0
    assert all(sum(w*d**s for w,d in zip(weights,divisors))==0
               for s in (3,5,7))
    kappa=sum(w*d**9 for w,d in zip(weights,divisors))
    assert kappa==a["kappa9"]
    B_d=[sum((constants[shift*D//d-1] for shift in range(1,d+1)),fmpq(0))
         for d in divisors]
    assert B_d==[q(v) for v in a["B_d"]]
    A=rho[8]*kappa
    B=sum((w*v for w,v in zip(weights,B_d)),fmpq(0))
    assert [A,B]==[q(v) for v in a["raw_A_B"]]
    denominator=math.lcm(int(A.denom()),int(B.denom()))
    pre=[int((A*denominator).numer()),int((B*denominator).numer())]
    content=math.gcd(*pre)
    pair=[x//content for x in pre]
    multiplier=fmpq(denominator,content)
    assert denominator==int(a["raw_denominator"])
    assert pre==[int(v) for v in a["preprimitive_A_B"]]
    assert content==int(a["content"])
    assert pair==[int(v) for v in a["primitive_A_B"]]
    assert multiplier==q(a["primitive_multiplier"]) and multiplier>0
    assert [multiplier*A,multiplier*B]==[fmpq(v) for v in pair]
    assert (A==0)==a["target_coefficient_zero"]
    sha=hashlib.sha256(",".join(map(str,pair)).encode()).hexdigest()
    assert sha==a["primitive_sha256"]==row["primitive_sha256"]
    for name,path in (
        ("tail_shift",ROOT/"missions/zeta9/round3/scripts/tail_shift.py"),
        ("general_poles",ROOT/"missions/zeta9/round2/scripts/general_poles.py"),
        ("shift_forms",ROOT/"missions/zeta9/round3/scripts/shift_forms.py")):
        assert hashlib.sha256(path.read_bytes()).hexdigest()==a["source_sha256"][name]
    bits=max(abs(v).bit_length() for v in pair)+500
    with ctx.workprec(bits):
        value=arb(fmpz(pair[1]))+arb(fmpz(pair[0]))*arb(9).zeta()
        sign=1 if value.lower()>0 else (-1 if value.upper()<0 else 0)
        assert sign==a["arb"]["sign"]==row["sign"]
        assert value.rel_accuracy_bits()>=80
        log_primitive=(value if sign>0 else -value).log()
        raw=value/arb(multiplier)
        raw_log=(raw if sign>0 else -raw).log()
        m_log=arb(multiplier).log()
        assert (raw_log+m_log).overlaps(log_primitive)
        assert bool(log_primitive.lower()>0)==a["arb"]["above_one"]
        assert bool(log_primitive.upper()<0)==a["arb"]["below_one"]
        return {"case_id":a["case_id"],"D":D,"n":n,"m":m,
                "target_coefficient_zero":A==0,"sign":sign,
                "raw_below_one":bool(raw_log.upper()<0),
                "primitive_above_one":bool(log_primitive.lower()>0),
                "log_raw_per_n":float(raw_log)/n,
                "log_multiplier_per_n":float(m_log)/n,
                "log_primitive_per_n":float(log_primitive)/n,
                "primitive_sha256":sha}


def main() -> None:
    source=VERIFY/"tail-shift-results.jsonl"
    rows=[json.loads(line) for line in source.read_text(encoding="utf-8").splitlines()
          if line.strip()]
    latest={row["case_id"]:row for row in rows}
    results=[audit(row) for row in latest.values() if row["status"]=="ok"]
    results.sort(key=lambda row:(row["n"],row["D"]))
    assert len(results)==6
    report={"status":"ok","records":len(results),
            "raw_below_one":sum(row["raw_below_one"] for row in results),
            "primitive_above_one":sum(row["primitive_above_one"] for row in results),
            "target_coefficient_zero":sum(row["target_coefficient_zero"] for row in results),
            "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "rows":results}
    (VERIFY/"tail-shift-audit.json").write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps({k:report[k] for k in ("status","records","raw_below_one",
                                            "primitive_above_one","target_coefficient_zero")},
                     ensure_ascii=False))


if __name__=="__main__":
    main()
