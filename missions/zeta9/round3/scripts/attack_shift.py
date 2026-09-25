"""Resumable, bounded scan of 25 rational-shift forms (two workers maximum)."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
VERIFY = ROOT / "missions/zeta9/round3/verification"
INDEX = VERIFY / "shift-results.jsonl"
WORKER = Path(__file__).with_name("shift_forms.py")


def cases() -> list[tuple[int,int,int]]:
    return [(D,n,m) for n in (6,12,24) for D in (6,8)
            for m in range(((10-D)*n+7)//(2*D)+1)]


def case_id(D:int,n:int,m:int) -> str:
    return f"D{D}-n{n}-m{m}"


def previous() -> dict[str,dict]:
    if not INDEX.exists():
        return {}
    records={}
    for line in INDEX.read_text(encoding="utf-8").splitlines():
        if line.strip():
            row=json.loads(line)
            records[row["case_id"]]=row
    return records


def execute(D:int,n:int,m:int,deadline:int) -> dict:
    started=time.monotonic()
    args=[sys.executable,str(WORKER),"--D",str(D),"--n",str(n),"--m",str(m),
          "--check-points"]
    base={"case_id":case_id(D,n,m),"D":D,"n":n,"m":m}
    try:
        result=subprocess.run(args,cwd=ROOT,capture_output=True,text=True,
                              encoding="utf-8",errors="replace",timeout=deadline)
        if result.returncode:
            return {**base,"status":"error",
                    "seconds":round(time.monotonic()-started,3),
                    "error":(result.stderr or result.stdout)[-2500:]}
        row=json.loads(result.stdout.strip().splitlines()[-1])
        if row["case_id"] != base["case_id"]:
            raise AssertionError("Subprocess returned a different case")
        row["runner_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        return row
    except subprocess.TimeoutExpired:
        return {**base,"status":"timeout","deadline_seconds":deadline,
                "seconds":round(time.monotonic()-started,3)}
    except Exception as exc:
        return {**base,"status":"error","error":repr(exc),
                "seconds":round(time.monotonic()-started,3)}


def append(row:dict) -> None:
    VERIFY.mkdir(parents=True,exist_ok=True)
    with INDEX.open("a",encoding="utf-8") as stream:
        stream.write(json.dumps(row,ensure_ascii=False,separators=(",",":"))+"\n")
    print(json.dumps({k:row[k] for k in ("case_id","status","sign","below_one",
                                          "log_abs_per_n","seconds","error")
                      if k in row},ensure_ascii=False),flush=True)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds",type=int,default=120)
    parser.add_argument("--workers",type=int,default=2)
    parser.add_argument("--retry-failed",action="store_true")
    args=parser.parse_args()
    if args.seconds<1 or not 1<=args.workers<=2:
        parser.error("Require seconds>=1 and 1<=workers<=2")
    history=previous()
    planned=cases()
    assert len(planned)==25
    todo=[c for c in planned if case_id(*c) not in history
          or (args.retry_failed and history[case_id(*c)]["status"] != "ok")]
    if todo:
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures={pool.submit(execute,*case,args.seconds):case for case in todo}
            for future in as_completed(futures):
                row=future.result()
                history[row["case_id"]]=row
                append(row)
    successful=[history.get(case_id(*c)) for c in planned]
    successful=[row for row in successful if row and row["status"]=="ok"]
    summary={"planned":len(planned),"ok":len(successful),
             "below_one":sum(row["below_one"] for row in successful),
             "negative":sum(row["sign"]<0 for row in successful),
             "status_counts":{status:sum(history.get(case_id(*c),{}).get("status")==status
                                          for c in planned)
                              for status in sorted({history.get(case_id(*c),{}).get("status")
                                                    for c in planned})},
             "best_log_per_n":sorted(({"case_id":row["case_id"],
                                      "log_abs_per_n":row["log_abs_per_n"]}
                                     for row in successful),key=lambda x:x["log_abs_per_n"])[:6]}
    print(json.dumps(summary,ensure_ascii=False),flush=True)


if __name__=="__main__":
    main()
