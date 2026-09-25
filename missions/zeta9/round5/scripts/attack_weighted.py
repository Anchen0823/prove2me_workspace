"""Resume the fixed 14+2 weighted-polynomial blocks, with two workers maximum."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[4]
VERIFY=ROOT/"missions/zeta9/round5/verification"
INDEX=VERIFY/"weighted-results.jsonl"
WORKER=Path(__file__).with_name("weighted_forms.py")


def planned() -> list[tuple[int,int,int,int,str]]:
    jobs=[]
    for n in (12,24):
        jobs.append((9,n,n,3,"regression"))
        jobs.extend((p,n,m,R,"new") for p,m,R in
                    ((9,n,4),(9,n,6),(9,n,8),
                     (7,n//2,2),(7,n//2,3),
                     (5,n//4,1),(5,n//4,2)))
    assert len(jobs)==16 and sum(j[4]=="new" for j in jobs)==14
    return jobs


def case_id(job:tuple) -> str:
    p,n,m,R=job[:4]
    return f"p{p}-n{n}-m{m}-R{R}"


def previous() -> dict[str,dict]:
    if not INDEX.exists():
        return {}
    result={}
    for line in INDEX.read_text(encoding="utf-8").splitlines():
        if line.strip():
            row=json.loads(line)
            result[row["case_id"]]=row
    return result


def run(job:tuple,seconds:int) -> dict:
    p,n,m,R,role=job
    started=time.monotonic()
    cmd=[sys.executable,str(WORKER),"--p",str(p),"--n",str(n),
         "--m",str(m),"--R",str(R)]
    try:
        process=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True,
                               encoding="utf-8",errors="replace",timeout=seconds)
        if process.returncode:
            return {"case_id":case_id(job),"role":role,"p":p,"n":n,"m":m,"R":R,
                    "status":"error","seconds":round(time.monotonic()-started,3),
                    "error":(process.stderr or process.stdout)[-2600:]}
        row=json.loads(process.stdout.strip().splitlines()[-1])
        if row["case_id"]!=case_id(job):
            raise AssertionError("Wrong case returned from subprocess")
        row["role"]=role
        row["runner_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        return row
    except subprocess.TimeoutExpired:
        return {"case_id":case_id(job),"role":role,"p":p,"n":n,"m":m,"R":R,
                "status":"timeout","deadline_seconds":seconds,
                "seconds":round(time.monotonic()-started,3)}
    except Exception as exc:
        return {"case_id":case_id(job),"role":role,"p":p,"n":n,"m":m,"R":R,
                "status":"error","seconds":round(time.monotonic()-started,3),
                "error":repr(exc)}


def append(row:dict) -> None:
    VERIFY.mkdir(parents=True,exist_ok=True)
    with INDEX.open("a",encoding="utf-8") as stream:
        stream.write(json.dumps(row,ensure_ascii=False,separators=(",",":"))+"\n")
    print(json.dumps({k:row[k] for k in
                      ("case_id","role","status","low_rank","full_rank",
                       "full_zero_rank","image_rank","selected_count",
                       "best_height_bits","best_log_abs_per_n","best_below_one",
                       "best_W_log_unweighted_l1_per_n","seconds","error")
                      if k in row},ensure_ascii=False),flush=True)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds",type=int,default=120)
    parser.add_argument("--workers",type=int,default=2)
    parser.add_argument("--retry-failed",action="store_true")
    parser.add_argument("--extend-p9-r4-n48",action="store_true",
                        help="Run the explicitly authorized single n=48 extension")
    args=parser.parse_args()
    if args.seconds<1 or not 1<=args.workers<=2:
        parser.error("Require seconds>=1 and 1<=workers<=2")
    jobs=planned()
    if args.extend_p9_r4_n48:
        jobs.append((9,48,48,4,"extension"))
    old=previous()
    worker_sha=hashlib.sha256(WORKER.read_bytes()).hexdigest()
    pending=[job for job in jobs if case_id(job) not in old
             or (args.retry_failed and old[case_id(job)]["status"]!="ok")
             or (old[case_id(job)].get("source_sha256") or {}).get("weighted_forms")!=worker_sha]
    if pending:
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures={pool.submit(run,job,args.seconds):job for job in pending}
            for future in as_completed(futures):
                row=future.result()
                old[row["case_id"]]=row
                append(row)
    records=[old.get(case_id(job)) for job in jobs]
    ok=[r for r in records if r and r["status"]=="ok"]
    summary={"planned":len(jobs),"new_blocks":14,"regressions":2,
             "extensions":int(args.extend_p9_r4_n48),
             "ok":len(ok),"new_ok":sum(r["role"]=="new" for r in ok),
             "regression_ok":sum(r["role"]=="regression" for r in ok),
             "any_below_one":sum(r["any_below_one"] for r in ok),
             "unresolved":[{"case_id":case_id(job),"status":None if row is None else row["status"]}
                           for job,row in zip(jobs,records) if row is None or row["status"]!="ok"]}
    print(json.dumps(summary,ensure_ascii=False),flush=True)


if __name__=="__main__":
    main()
