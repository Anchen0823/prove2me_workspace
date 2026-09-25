"""Small-prime denominator audit and large-prime top-residue scan for round 3.

No integer factorization black box and no large partial-fraction computation are
used in the 10-case scan.  A zero modular residue is left undecided.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys
import time

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"tmp/zeta7/exact_packages"))
from flint import fmpq  # type: ignore

VERIFY=ROOT/"missions/zeta9/round4/verification"
TAIL=ROOT/"missions/zeta9/round3/verification"
WEIGHTS={6:([1,2,3,6],[-7776,1701,-224,1]),
         8:([1,2,4,8],[-32768,5376,-168,1])}


def primes_through(limit:int) -> list[int]:
    sieve=bytearray(b"\x01")*(limit+1)
    sieve[0:2]=b"\x00\x00"
    for p in range(2,math.isqrt(limit)+1):
        if sieve[p]:
            sieve[p*p:limit+1:p]=b"\x00"*((limit-p*p)//p+1)
    return [p for p in range(2,limit+1) if sieve[p]]


def coeffs(n:int) -> list[int]:
    return [(-1)**j*math.comb(n,j)**9
            *math.comb(n+j,n)*math.comb(2*n-j,n)
            for j in range(n+1)]


def coeff_sha(C:list[int]) -> str:
    return hashlib.sha256(",".join(map(str,C)).encode()).hexdigest()


def band(D:int,n:int,p:int) -> str:
    if p<=n:
        return "p_le_n"
    if p<=2*n:
        return "n_lt_p_le_2n"
    if p<=D*n:
        return "2n_lt_p_le_Dn"
    if p<=2*D*n:
        return "Dn_lt_p_le_2Dn"
    return "above_2Dn"


def factor_to_bound(value:int,primes:list[int]) -> tuple[dict[int,int],int]:
    remaining=abs(value)
    if remaining==0:
        raise ValueError("Cannot factor zero")
    powers={}
    for p in primes:
        count=0
        while remaining%p==0:
            count+=1
            remaining//=p
        if count:
            powers[p]=count
    return powers,remaining


def vp(value:int,p:int) -> int:
    value=abs(value)
    if value==0:
        raise ValueError("Zero has no finite valuation")
    result=0
    while value%p==0:
        result+=1
        value//=p
    return result


def modular_contributions(D:int,n:int,C:list[int],p:int) -> tuple[list[int],int]:
    if not (2*n<p<=2*D*n and p*p>2*D*n):
        raise ValueError("Top-residue formula only established in large-prime range")
    divisors,weights=WEIGHTS[D]
    H=[0]
    for ell in range(1,D+1):
        H.append((H[-1]+pow(pow(ell,-1,p),9,p))%p)
    contributions=[]
    for d,w in zip(divisors,weights):
        inner=sum((C[j]%p)*H[d*(j+n)//p] for j in range(n+1))%p
        contributions.append((-w*pow(d,9,p)*inner)%p)
    return contributions,sum(contributions)%p


def q(pair:list[str]) -> fmpq:
    return fmpq(int(pair[0]),int(pair[1]))


def archive_one(D:int,n:int) -> dict:
    m=n
    path=TAIL/f"tail-shift-D{D}-n{n}-m{m}.json.gz"
    with gzip.open(path,"rt",encoding="utf-8") as stream:
        data=json.load(stream)
    assert data["D"]==D and data["n"]==n and data["m"]==m
    A,B=map(q,data["raw_A_B"])
    Q=int(B.denom())
    M=q(data["primitive_multiplier"])
    full_primes=primes_through(2*D*n)
    den_factor,den_remainder=factor_to_bound(Q,full_primes)
    Mnum_factor,Mnum_remainder=factor_to_bound(int(M.numer()),full_primes)
    Mden_factor,Mden_remainder=factor_to_bound(int(M.denom()),full_primes)
    signed={p:Mnum_factor.get(p,0)-Mden_factor.get(p,0)
            for p in full_primes}
    signed={p:v for p,v in signed.items() if v}
    bands={name:{"positive_log_per_n":0.0,"negative_log_per_n":0.0,
                 "signed_log_per_n":0.0,"nonzero_valuations":0,
                 "valuations":[]} for name in
           ("p_le_n","n_lt_p_le_2n","2n_lt_p_le_Dn","Dn_lt_p_le_2Dn")}
    for p,v in signed.items():
        group=bands[band(D,n,p)]
        cost=v*math.log(p)/n
        group["signed_log_per_n"]+=cost
        group["positive_log_per_n"]+=max(cost,0)
        group["negative_log_per_n"]+=min(cost,0)
        group["nonzero_valuations"]+=1
        group["valuations"].append([p,v])

    C=coeffs(n)
    assert [int(data["pole_coefficients_j_by_s1_to9"][j][8][0])
            for j in range(n+1)]==C
    checks=[]
    for p in full_primes:
        if p<=2*n:
            continue
        contributions,residue=modular_contributions(D,n,C,p)
        scaled=fmpq(p**9)*B
        den=int(scaled.denom())
        assert den%p!=0
        exact=int(scaled.numer())*pow(den,-1,p)%p
        assert exact==residue
        valuation=vp(int(B.numer()),p)-vp(int(B.denom()),p)
        assert valuation==-9 if residue else valuation>=-8
        checks.append({"p":p,"band":band(D,n,p),
                       "contributions_by_divisor_mod_p":contributions,
                       "formula_residue_mod_p":residue,
                       "exact_p9_B_mod_p":exact,
                       "nonzero":bool(residue),"exact_vp_B":valuation})
    logM=math.log(int(M.numer()))-math.log(int(M.denom()))
    known=sum(v*math.log(p) for p,v in signed.items())
    residual_log=math.log(Mnum_remainder)-math.log(Mden_remainder)
    assert abs((known+residual_log)-logM)<1e-9*max(1,abs(logM))
    return {"case_id":data["case_id"],"D":D,"n":n,"m":m,
            "B_denominator":str(Q),"B_denominator_prime_powers":
                [[p,v] for p,v in sorted(den_factor.items())],
            "B_denominator_residual":str(den_remainder),
            "B_denominator_sha256":hashlib.sha256(str(Q).encode()).hexdigest(),
            "primitive_multiplier":data["primitive_multiplier"],
            "primitive_multiplier_positive_powers":
                [[p,v] for p,v in sorted(Mnum_factor.items())],
            "primitive_multiplier_negative_powers":
                [[p,v] for p,v in sorted(Mden_factor.items())],
            "primitive_multiplier_num_residual":str(Mnum_remainder),
            "primitive_multiplier_den_residual":str(Mden_remainder),
            "content":data["content"],"C_sha256":coeff_sha(C),
            "band_costs":bands,"log_multiplier_per_n":logM/n,
            "large_prime_mod_checks":checks,
            "large_prime_check_count":len(checks),
            "nonzero_large_prime_count":sum(row["nonzero"] for row in checks),
            "zero_large_prime_count":sum(not row["nonzero"] for row in checks),
            "source_tail_sha256":data["source_sha256"]}


def run_archive() -> None:
    rows=[archive_one(D,n) for n in (6,12,24) for D in (6,8)]
    assert all(row["B_denominator_residual"]=="1" and
               row["primitive_multiplier_num_residual"]=="1" and
               row["primitive_multiplier_den_residual"]=="1" for row in rows)
    assert all(row["content"]=="1" and
               not row["primitive_multiplier_negative_powers"] for row in rows)
    report={"status":"ok","cases":len(rows),
            "large_prime_mod_checks":sum(row["large_prime_check_count"] for row in rows),
            "all_denominators_completely_trial_factored":True,
            "all_primitive_multiplier_negative_valuations_empty":True,
            "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "rows":rows}
    VERIFY.mkdir(parents=True,exist_ok=True)
    (VERIFY/"prime-archive-audit.json").write_text(
        json.dumps(report,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps({"archive_cases":len(rows),
                      "large_prime_mod_checks":report["large_prime_mod_checks"],
                      "status":"ok"}),flush=True)


def scan_one(D:int,n:int) -> dict:
    C=coeffs(n)
    primes=primes_through(2*D*n)
    records=[]
    for p in primes:
        if p<=2*n:
            continue
        contributions,residue=modular_contributions(D,n,C,p)
        records.append({"p":p,"band":band(D,n,p),
                        "contributions_by_divisor_mod_p":contributions,
                        "residue_mod_p":residue,"nonzero":bool(residue),
                        "vp_B_conclusion":"-9" if residue else "undetermined"})
    boundaries=("2n_lt_p_le_Dn","Dn_lt_p_le_2Dn")
    summary={name:{"primes":sum(row["band"]==name for row in records),
                   "nonzero":sum(row["band"]==name and row["nonzero"] for row in records),
                   "zero_unresolved_primes":[row["p"] for row in records
                                             if row["band"]==name and not row["nonzero"]]}
             for name in boundaries}
    artifact={"case_id":f"D{D}-n{n}","D":D,"n":n,
              "definition":"tail-p9-m=n-large-prime-S-v1",
              "formula":"S_p=-sum_j C_j sum_d w_d d^9 H_floor(d(j+n)/p)^(9) mod p",
              "divisors":WEIGHTS[D][0],"weights":WEIGHTS[D][1],
              "C_definition":"(-1)^j binom(n,j)^9 binom(n+j,n) binom(2n-j,n)",
              "C_sha256":coeff_sha(C),"prime_limit":2*D*n,
              "large_prime_condition":"p>2n, p^2>2Dn, p does not divide D",
              "summary":summary,"prime_records":records,
              "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    path=VERIFY/f"prime-scan-D{D}-n{n}.json.gz"
    with gzip.open(path,"wt",encoding="utf-8",compresslevel=6) as stream:
        json.dump(artifact,stream,ensure_ascii=False,separators=(",",":"))
    return {"case_id":artifact["case_id"],"D":D,"n":n,
            "artifact":str(path.relative_to(ROOT)),"C_sha256":artifact["C_sha256"],
            "summary":summary,
            "large_primes":len(records),
            "nonzero":sum(row["nonzero"] for row in records),
            "zero_unresolved":sum(not row["nonzero"] for row in records)}


def run_scan(retry:bool=False) -> None:
    VERIFY.mkdir(parents=True,exist_ok=True)
    path=VERIFY/"prime-scan-summary.json"
    if path.exists() and not retry:
        old=json.loads(path.read_text(encoding="utf-8"))
        rows={row["case_id"]:row for row in old.get("rows",[])}
    else:
        rows={}
    started=time.monotonic()
    for n in (24,48,96,192,384):
        for D in (6,8):
            key=f"D{D}-n{n}"
            if key not in rows:
                row=scan_one(D,n)
                rows[key]=row
                report={"status":"partial","cases_done":len(rows),
                        "planned":10,"rows":list(rows.values())}
                path.write_text(json.dumps(report,ensure_ascii=False,indent=2),
                                encoding="utf-8")
                print(json.dumps({"case_id":key,"large_primes":row["large_primes"],
                                  "nonzero":row["nonzero"],
                                  "zero_unresolved":row["zero_unresolved"]}),flush=True)
    result={"status":"ok","planned":10,"cases_done":len(rows),
            "large_primes":sum(row["large_primes"] for row in rows.values()),
            "nonzero":sum(row["nonzero"] for row in rows.values()),
            "zero_unresolved":sum(row["zero_unresolved"] for row in rows.values()),
            "seconds":round(time.monotonic()-started,3),
            "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "rows":list(rows.values())}
    path.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps({k:result[k] for k in ("status","cases_done","large_primes",
                                           "nonzero","zero_unresolved","seconds")}),flush=True)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive-only",action="store_true")
    parser.add_argument("--scan-only",action="store_true")
    parser.add_argument("--retry",action="store_true")
    args=parser.parse_args()
    if args.archive_only and args.scan_only:
        parser.error("Choose at most one mode")
    if not args.scan_only:
        run_archive()
    if not args.archive_only:
        run_scan(args.retry)


if __name__=="__main__":
    main()
