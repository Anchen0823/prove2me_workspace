"""Bounded, resumable exact odd-zeta linear-form campaign.

Each case runs in a separate Python process with a 120-second deadline.
The index is append-only; completed cases are skipped on resume.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[3]
SCRIPT=Path(__file__).with_name("odd_linear_form.py")
INDEX=ROOT/"missions/zeta9/verification/linear-results.jsonl"
PROFILES=(Fraction(1,28),Fraction(1,14),Fraction(3,28),
          Fraction(1,7),Fraction(5,28),Fraction(3,14))
SCALES=(56,112,224)


def key(n:int,m:int,s:int=9) -> str:
    return f"s{s}-n{n}-m{m}"


def cases() -> list[tuple[int,int,str]]:
    output=[]
    for n in SCALES:
        for alpha in PROFILES:
            m=alpha*n
            assert m.denominator==1
            output.append((n,int(m),"grid"))
        output.append((n,0,"control"))
    return output


def existing() -> dict[str,dict]:
    if not INDEX.exists():
        return {}
    latest={}
    for line in INDEX.read_text(encoding="utf-8").splitlines():
        if line.strip():
            row=json.loads(line)
            latest[row["case_id"]]=row
    return latest


def run_one(n:int,m:int,case_type:str,seconds:int) -> dict:
    start=time.monotonic()
    cmd=[sys.executable,str(SCRIPT),"--compute","--s","9","--n",str(n),
         "--m",str(m),"--case-type",case_type]
    try:
        proc=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True,
                            encoding="utf-8",errors="replace",timeout=seconds)
        if proc.returncode:
            return {"case_id":key(n,m),"s":9,"n":n,"m":m,
                    "r":3*n+1-14*m,"case_type":case_type,"status":"error",
                    "seconds":round(time.monotonic()-start,3),
                    "error":proc.stderr[-2500:] or proc.stdout[-2500:]}
        row=json.loads(proc.stdout.strip().splitlines()[-1])
        if row["case_id"]!=key(n,m) or row["status"]!="ok":
            raise AssertionError("Child returned a mismatched case")
        return row
    except subprocess.TimeoutExpired:
        return {"case_id":key(n,m),"s":9,"n":n,"m":m,
                "r":3*n+1-14*m,"case_type":case_type,"status":"timeout",
                "seconds":round(time.monotonic()-start,3),"deadline_seconds":seconds}
    except Exception as exc:
        return {"case_id":key(n,m),"s":9,"n":n,"m":m,
                "r":3*n+1-14*m,"case_type":case_type,"status":"error",
                "seconds":round(time.monotonic()-start,3),"error":repr(exc)}


def append(row:dict) -> None:
    INDEX.parent.mkdir(parents=True,exist_ok=True)
    with INDEX.open("a",encoding="utf-8") as stream:
        stream.write(json.dumps(row,ensure_ascii=False,separators=(",",":"))+"\n")
    print(json.dumps({k:row.get(k) for k in ("case_id","status","r","sign",
                                                 "below_one","abs_log_per_n",
                                                 "height_digits","seconds","error")
                      if k in row},ensure_ascii=False),flush=True)


def advance(rows:dict[str,dict]) -> list[tuple[int,int,str]]:
    ranks=[]
    for alpha in PROFILES:
        profile=[]
        for n in SCALES:
            case=key(n,int(alpha*n))
            row=rows.get(case)
            if row is None or row["status"]!="ok":
                profile=[]
                break
            profile.append(row)
        if not profile:
            continue
        last_two_below=profile[1]["below_one"] and profile[2]["below_one"]
        strictly_falling=(profile[0]["abs_log_per_n"]
                          >profile[1]["abs_log_per_n"]
                          >profile[2]["abs_log_per_n"])
        if not (last_two_below or strictly_falling):
            continue
        priority=0 if last_two_below else 1
        ranks.append((priority,profile[2]["abs_log_per_n"],
                      profile[2]["height_digits"],alpha))
    ranks.sort()
    return [(448,int(alpha*448),"extension") for _,_,_,alpha in ranks[:2]]


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds",type=int,default=120)
    parser.add_argument("--workers",type=int,default=2)
    parser.add_argument("--primary-only",action="store_true")
    parser.add_argument("--retry-failed",action="store_true")
    args=parser.parse_args()
    if args.seconds<1 or not 1<=args.workers<=2:
        parser.error("Require seconds>=1 and 1<=workers<=2")
    rows=existing()
    def run_batch(batch:list[tuple[int,int,str]]) -> None:
        todo=[c for c in batch if key(*c[:2]) not in rows
              or (args.retry_failed and rows[key(*c[:2])]["status"]!="ok")]
        if not todo:
            return
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            future={pool.submit(run_one,*c,args.seconds):c for c in todo}
            for f in as_completed(future):
                row=f.result()
                rows[row["case_id"]]=row
                append(row)
    for n in SCALES:
        run_batch([c for c in cases() if c[0]==n])
    if not args.primary_only:
        run_batch(advance(rows))
    counts={status:sum(row["status"]==status for row in rows.values())
            for status in ("ok","timeout","error")}
    print(json.dumps({"cases_total":len(rows),"counts":counts,
                      "extension_candidates":advance(rows)},ensure_ascii=False),flush=True)


if __name__=="__main__":
    main()
