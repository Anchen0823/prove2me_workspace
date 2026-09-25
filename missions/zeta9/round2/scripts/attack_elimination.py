"""Resumable bounded search over pole orders and exact cofactor elimination.

The primary campaign has 58 windows; each atom or combination is a separate
process with a 120-second deadline. At most two processes run concurrently.
Use --extend only after reviewing the primary stage; at most two slots advance.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
import json
import math
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[4]
VERIFY=ROOT/"missions/zeta9/round2/verification"
SCRIPT=Path(__file__).with_name("general_poles.py")
ATOM_INDEX=VERIFY/"elimination-atoms.jsonl"
COMBO_INDEX=VERIFY/"elimination-results.jsonl"
POLES=(3,5,7,9)
PRIMARY=(12,24,48)


def m_max(p:int,n:int) -> int:
    b=10-p
    return (p*(n+1)-2)//(2*b)


def windows(p:int,n:int) -> list[tuple[int,int]]:
    q=(p-1)//2
    maximum=m_max(p,n)-q+1
    if maximum<0:
        return []
    output=[]
    seen=set()
    for slot in range(5):
        # Rational half-up rounding keeps the profile deterministic.
        start=(maximum*slot+2)//4
        if start not in seen:
            output.append((slot,start))
            seen.add(start)
    return output


def profile_start(p:int,n:int,slot:int) -> int:
    if p==9 and slot==5:
        # Extra theoretically motivated m=n profile, kept outside the 58 grid.
        return n
    return next(m for k,m in windows(p,n) if k==slot)


def atom_case(p:int,n:int,m:int) -> str:
    return f"p{p}-n{n}-m{m}"


def combo_case(p:int,n:int,start:int) -> str:
    q=(p-1)//2
    return f"p{p}-n{n}-m{start}..{start+q-1}"


def existing(path:Path) -> dict[str,dict]:
    if not path.exists():
        return {}
    latest={}
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            row=json.loads(line)
            latest[row["case_id"]]=row
    return latest


def append(path:Path,row:dict) -> None:
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open("a",encoding="utf-8") as stream:
        stream.write(json.dumps(row,ensure_ascii=False,separators=(",",":"))+"\n")
    print(json.dumps({k:row[k] for k in ("case_id","status","p","n","m",
                                          "m_start","profile_slot","sign","below_one",
                                          "abs_log_per_n","height_digits","seconds","error")
                      if k in row},ensure_ascii=False),flush=True)


def child(cmd:list[str],case:str,p:int,n:int,extra:dict,seconds:int) -> dict:
    start=time.monotonic()
    args=[sys.executable,str(SCRIPT)]+cmd
    try:
        proc=subprocess.run(args,cwd=ROOT,capture_output=True,text=True,
                            encoding="utf-8",errors="replace",timeout=seconds)
        if proc.returncode:
            return {"case_id":case,"p":p,"n":n,**extra,"status":"error",
                    "seconds":round(time.monotonic()-start,3),
                    "error":proc.stderr[-2200:] or proc.stdout[-2200:]}
        row=json.loads(proc.stdout.strip().splitlines()[-1])
        if row["case_id"]!=case:
            raise AssertionError("Child returned the wrong case")
        return row
    except subprocess.TimeoutExpired:
        return {"case_id":case,"p":p,"n":n,**extra,"status":"timeout",
                "seconds":round(time.monotonic()-start,3),"deadline_seconds":seconds}
    except Exception as exc:
        return {"case_id":case,"p":p,"n":n,**extra,"status":"error",
                "seconds":round(time.monotonic()-start,3),"error":repr(exc)}


def atom_job(p:int,n:int,m:int,seconds:int) -> dict:
    return child(["--atom","--p",str(p),"--n",str(n),"--m",str(m)],
                 atom_case(p,n,m),p,n,{"m":m},seconds)


def combo_job(p:int,n:int,start:int,slot:int,seconds:int) -> dict:
    return child(["--combine","--p",str(p),"--n",str(n),"--start",str(start),
                  "--slot",str(slot)],combo_case(p,n,start),p,n,
                 {"m_start":start,"profile_slot":slot},seconds)


def run_jobs(jobs:list[tuple],fn,index:Path,latest:dict,
             workers:int,seconds:int,retry_failed:bool) -> None:
    stable={"ok","rank_deficient","constant_only","zero_combination"}
    todo=[]
    for job in jobs:
        case=(atom_case(*job) if fn is atom_job else combo_case(job[0],job[1],job[2]))
        previous=latest.get(case)
        if previous is None or (retry_failed and previous["status"] not in stable):
            todo.append(job)
    if not todo:
        return
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures={pool.submit(fn,*job,seconds):job for job in todo}
        for future in as_completed(futures):
            row=future.result()
            latest[row["case_id"]]=row
            append(index,row)


def stage(n:int,atoms:dict,combos:dict,workers:int,seconds:int,
          retry_failed:bool,selected:list[tuple[int,int]]|None=None) -> None:
    selected=selected if selected is not None else [(p,slot)
                    for p in POLES for slot,_ in windows(p,n)]+[(9,5)]
    profiles=[]
    for p,slot in selected:
        start=profile_start(p,n,slot)
        profiles.append((p,n,start,slot))
    atom_set=sorted({(p,n,m) for p,_,start,_ in profiles
                     for m in range(start,start+(p-1)//2)})
    run_jobs(atom_set,atom_job,ATOM_INDEX,atoms,workers,seconds,retry_failed)
    ready=[]
    for p,_,start,slot in profiles:
        inputs=[atoms.get(atom_case(p,n,m)) for m in range(start,start+(p-1)//2)]
        if all(row is not None and row["status"]=="ok" for row in inputs):
            ready.append((p,n,start,slot))
        else:
            case=combo_case(p,n,start)
            if case not in combos:
                row={"case_id":case,"p":p,"n":n,"m_start":start,
                     "profile_slot":slot,"status":"unresolved_input",
                     "input_statuses":[None if row is None else row["status"] for row in inputs]}
                combos[case]=row
                append(COMBO_INDEX,row)
    run_jobs(ready,combo_job,COMBO_INDEX,combos,workers,seconds,retry_failed)


def extension_candidates(combos:dict) -> list[tuple[int,int]]:
    eligible=[]
    for p in POLES:
        slots=[slot for slot,_ in windows(p,24)]+([5] if p==9 else [])
        for slot in slots:
            start24=profile_start(p,24,slot)
            try:
                start48=profile_start(p,48,slot)
            except StopIteration:
                continue
            row24=combos.get(combo_case(p,24,start24))
            row48=combos.get(combo_case(p,48,start48))
            if not row24 or not row48 or row24["status"]!="ok" or row48["status"]!="ok":
                continue
            below=row48["below_one"] or row24["below_one"]
            decreasing=row48["abs_log_per_n"]<row24["abs_log_per_n"]
            if not (below or decreasing):
                continue
            priority=0 if below else 1
            eligible.append((priority,row48["abs_log_per_n"],
                             row48["height_digits"],p,slot))
    eligible.sort()
    return [(p,slot) for _,_,_,p,slot in eligible[:2]]


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds",type=int,default=120)
    parser.add_argument("--workers",type=int,default=2)
    parser.add_argument("--extend",action="store_true")
    parser.add_argument("--retry-failed",action="store_true")
    args=parser.parse_args()
    if args.seconds<1 or not 1<=args.workers<=2:
        parser.error("Require seconds>=1, 1<=workers<=2")
    atoms=existing(ATOM_INDEX)
    combos=existing(COMBO_INDEX)
    for n in PRIMARY:
        stage(n,atoms,combos,args.workers,args.seconds,args.retry_failed)
    next_slots=extension_candidates(combos)
    print(json.dumps({"primary_windows":sum(len(windows(p,n)) for p in POLES for n in PRIMARY),
                      "extra_canonical_windows":len(PRIMARY),
                      "atom_records":len(atoms),"combination_records":len(combos),
                      "next_slots":[{"p":p,"slot":slot} for p,slot in next_slots]}),flush=True)
    if args.extend and next_slots:
        stage(96,atoms,combos,args.workers,args.seconds,args.retry_failed,next_slots)
    print(json.dumps({"atom_statuses":{status:sum(row["status"]==status for row in atoms.values())
                                       for status in sorted({row["status"] for row in atoms.values()})},
                      "combination_statuses":{status:sum(row["status"]==status for row in combos.values())
                                              for status in sorted({row["status"] for row in combos.values()})}}),flush=True)


if __name__=="__main__":
    main()
