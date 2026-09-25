"""Bounded six-case tail-shift experiment using the existing p=9 exact poles.

This is a new summation range: r_a = sum_{k=m}^infinity R(k+a/D), m=n.
The rational function itself is the round-two p=9, m=n function.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
import gzip
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys
import time

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"tmp/zeta7/exact_packages"))
sys.path.insert(0,str(ROOT/"missions/zeta9/round2/scripts"))
from flint import fmpq  # type: ignore
from general_poles import exact_vector  # type: ignore
from shift_forms import fixed_weights,qp,signed_arb  # type: ignore

VERIFY=ROOT/"missions/zeta9/round3/verification"
INDEX=VERIFY/"tail-shift-results.jsonl"


def case_id(D:int,n:int) -> str:
    return f"D{D}-n{n}-m{n}"


def model(D:int,n:int) -> dict:
    if D not in (6,8) or n not in (6,12,24):
        raise ValueError("Tail grid is D in {6,8}, n in {6,12,24}, m=n")
    m=n
    poles=exact_vector(9,n,m,check_points=True)["pole_coeffs"]
    rho={s:sum(poles[s],fmpq(0)) for s in range(1,10)}
    if any(rho[s] for s in (1,2,4,6,8)):
        raise AssertionError("Original p=9 pole symmetries failed")
    F=fmpq(math.factorial(n)**9,math.factorial(m)**2)
    for a in range(1,D+1):
        t=fmpq(m*D+a,D)
        numerator=(math.prod((t-r for r in range(1,m+1)),start=fmpq(1))
                   *math.prod((t+n+r for r in range(1,m+1)),start=fmpq(1)))
        direct=F*numerator/math.prod(((t+j)**9 for j in range(n+1)),start=fmpq(1))
        partial=sum((poles[s][j]/(t+j)**s
                     for s in range(1,10) for j in range(n+1)),fmpq(0))
        if direct!=partial or direct<=0:
            raise AssertionError("Shifted first summand/PF positivity check failed")
    B_a=[]
    for a in range(1,D+1):
        harmonic={s:[fmpq(0)] for s in range(1,10)}
        for j in range(1,n+m+1):
            for s in range(1,10):
                harmonic[s].append(harmonic[s][-1]+fmpq(D,D*(j-1)+a)**s)
        B_a.append(-sum((poles[s][j]*harmonic[s][j+m]
                         for s in range(1,10) for j in range(n+1)),fmpq(0)))
    divisors,weights,kappa=fixed_weights(D)
    B_d=[sum((B_a[a*D//d-1] for a in range(1,d+1)),fmpq(0))
         for d in divisors]
    A=rho[9]*kappa
    B=sum((weights[i]*B_d[i] for i in range(4)),fmpq(0))
    denominator=math.lcm(int(A.denom()),int(B.denom()))
    pre=[int((A*denominator).numer()),int((B*denominator).numer())]
    content=math.gcd(*pre)
    primitive=[v//content for v in pre]
    multiplier=fmpq(denominator,content)
    assert content>0 and math.gcd(*primitive)==1
    assert [multiplier*A,multiplier*B]==[fmpq(v) for v in primitive]
    return {"D":D,"n":n,"m":m,"F":F,"poles":poles,"rho":rho,
            "B_a":B_a,"divisors":divisors,"weights":weights,"kappa":kappa,
            "B_d":B_d,"raw_A":A,"raw_B":B,
            "raw_denominator":denominator,"preprimitive":pre,
            "content":content,"primitive":primitive,"multiplier":multiplier}


def save(M:dict,seconds:float) -> dict:
    D,n,m=M["D"],M["n"],M["m"]
    case=case_id(D,n)
    scored=signed_arb(*M["primitive"])
    sha=hashlib.sha256(",".join(map(str,M["primitive"])).encode()).hexdigest()
    artifact={"case_id":case,"definition":"tail-shift-round2-p9-m=n-v1",
              "D":D,"n":n,"m":m,"tail_start_k":m,"F":qp(M["F"]),
              "pole_coefficients_j_by_s1_to9":
                  [[qp(M["poles"][s][j]) for s in range(1,10)]
                   for j in range(n+1)],
              "rho_s1_to9":[qp(M["rho"][s]) for s in range(1,10)],
              "B_a_a1_toD":[qp(v) for v in M["B_a"]],
              "divisors":M["divisors"],"weights":M["weights"],
              "kappa9":M["kappa"],"B_d":[qp(v) for v in M["B_d"]],
              "raw_A_B":[qp(M["raw_A"]),qp(M["raw_B"])],
              "raw_denominator":str(M["raw_denominator"]),
              "preprimitive_A_B":[str(v) for v in M["preprimitive"]],
              "content":str(M["content"]),"primitive_multiplier":qp(M["multiplier"]),
              "primitive_A_B":[str(v) for v in M["primitive"]],
              "target_coefficient_zero":M["raw_A"]==0,
              "primitive_sha256":sha,"arb":scored,"seconds":seconds,
              "source_sha256":{
                  "tail_shift":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  "general_poles":hashlib.sha256((ROOT/"missions/zeta9/round2/scripts/general_poles.py").read_bytes()).hexdigest(),
                  "shift_forms":hashlib.sha256(Path(__file__).with_name("shift_forms.py").read_bytes()).hexdigest()}}
    VERIFY.mkdir(parents=True,exist_ok=True)
    path=VERIFY/f"tail-shift-{case}.json.gz"
    with gzip.open(path,"wt",encoding="utf-8",compresslevel=6) as stream:
        json.dump(artifact,stream,ensure_ascii=False,separators=(",",":"))
    return {"case_id":case,"status":"ok","D":D,"n":n,"m":m,
            "artifact":str(path.relative_to(ROOT)),"primitive_sha256":sha,
            "primitive_multiplier":qp(M["multiplier"]),
            "target_coefficient_zero":M["raw_A"]==0,
            "sign":scored["sign"],"below_one":scored["below_one"],
            "above_one":scored["above_one"],"log_abs":scored["log_abs"],
            "log_abs_per_n":scored["log_abs"]/n,"seconds":seconds}


def run_one(D:int,n:int) -> dict:
    start=time.monotonic()
    result=model(D,n)
    return save(result,time.monotonic()-start)


def scan(seconds:int,workers:int,retry_failed:bool) -> None:
    history={}
    if INDEX.exists():
        for line in INDEX.read_text(encoding="utf-8").splitlines():
            if line.strip():
                row=json.loads(line)
                history[row["case_id"]]=row
    cases=[(D,n) for n in (6,12,24) for D in (6,8)]
    todo=[case for case in cases if case_id(*case) not in history
          or (retry_failed and history[case_id(*case)]["status"]!="ok")]
    def child(D:int,n:int) -> dict:
        start=time.monotonic()
        cmd=[sys.executable,str(Path(__file__)),"--D",str(D),"--n",str(n)]
        try:
            output=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True,
                                  encoding="utf-8",errors="replace",timeout=seconds)
            if output.returncode:
                return {"case_id":case_id(D,n),"D":D,"n":n,"m":n,
                        "status":"error","seconds":round(time.monotonic()-start,3),
                        "error":(output.stderr or output.stdout)[-2400:]}
            return json.loads(output.stdout.strip().splitlines()[-1])
        except subprocess.TimeoutExpired:
            return {"case_id":case_id(D,n),"D":D,"n":n,"m":n,
                    "status":"timeout","deadline_seconds":seconds,
                    "seconds":round(time.monotonic()-start,3)}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures={pool.submit(child,*case):case for case in todo}
        for future in as_completed(futures):
            row=future.result()
            history[row["case_id"]]=row
            VERIFY.mkdir(parents=True,exist_ok=True)
            with INDEX.open("a",encoding="utf-8") as stream:
                stream.write(json.dumps(row,ensure_ascii=False,separators=(",",":"))+"\n")
            print(json.dumps({k:row[k] for k in ("case_id","status","sign",
                                                  "below_one","log_abs_per_n",
                                                  "seconds","error") if k in row},
                             ensure_ascii=False),flush=True)
    ok=[history.get(case_id(*case)) for case in cases]
    ok=[row for row in ok if row and row["status"]=="ok"]
    print(json.dumps({"planned":6,"ok":len(ok),
                      "below_one":sum(row["below_one"] for row in ok),
                      "negative":sum(row["sign"]<0 for row in ok)},
                     ensure_ascii=False),flush=True)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--D",type=int)
    parser.add_argument("--n",type=int)
    parser.add_argument("--scan",action="store_true")
    parser.add_argument("--seconds",type=int,default=120)
    parser.add_argument("--workers",type=int,default=2)
    parser.add_argument("--retry-failed",action="store_true")
    args=parser.parse_args()
    if args.scan:
        if args.seconds<1 or not 1<=args.workers<=2:
            parser.error("Require seconds>=1 and 1<=workers<=2")
        scan(args.seconds,args.workers,args.retry_failed)
    else:
        if args.D is None or args.n is None:
            parser.error("--D and --n are required")
        print(json.dumps(run_one(args.D,args.n),ensure_ascii=False,separators=(",",":")),
              flush=True)


if __name__=="__main__":
    main()
