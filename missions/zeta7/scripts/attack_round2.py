"""Resumable exact round-two Hankel search. Finite evidence, not a proof.

Each candidate runs in a separate Python process with a 120 second deadline.
Successful full coefficient records are gzip files; the JSONL index is append-only.
Run from the workspace root with the bundled Python used by exact_hankel.py.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import time

from exact_hankel import ROOT, evaluate, parameters, record


VERIFY = ROOT / "missions/zeta7/verification"
INDEX = VERIFY / "round2-results.jsonl"
COEFF_DIR = VERIFY / "round2-coeff"
SCRIPT = Path(__file__).resolve()
EXACT = SCRIPT.with_name("exact_hankel.py")
PYTHON = sys.executable
MAX_WORKERS = 2
DEADLINE = 120


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def case_id(stage: str, route: str, layers40: list[dict], h40: int,
            shift40: int, s: int = 7) -> str:
    layer_text = "_".join(f"n{x['N40']}q{x['q']}" for x in layers40)
    return f"{stage}-{route}-s{s}-{layer_text}-h{h40}-g{shift40}"


def make_case(stage: str, route: str, layers40: list[dict], h40: int,
              shift40: int = 0, s: int = 7, source_case_id: str | None = None) -> dict:
    scale = {"K40": 1, "K80": 2, "K160": 4}[stage]
    K = 40 * scale
    h = h40 * scale
    g = shift40 * scale
    zeros = {}
    for layer in layers40:
        for j in range(1, layer["N40"] * scale + 1):
            zeros[j] = zeros.get(j, 0) + layer["q"]
    r = K - len(zeros)
    if h > r:
        raise ValueError("This round requires h <= pole count")
    # Route B translates the complete monomial block by g.
    exponents = list(range(g, g + h))
    return dict(case_id=case_id(stage, route, layers40, h40, shift40, s),
                stage=stage, route=route, s=s, K=K, h=h, r=r,
                h40=h40, lam_ratio=f"{h40}/40", layers40=layers40,
                basis_mode="whole_shift",
                shift40=shift40, g=g, qsum=sum(x["q"] for x in layers40),
                zeros=zeros, exponents=exponents, source_case_id=source_case_id)


def controls() -> list[dict]:
    return [make_case(stage, "C", [{"N40": 3, "q": 3}], 37, s=s)
            for stage in ("K40", "K80") for s in (5, 7)]


def route_a() -> list[dict]:
    out = []
    for n1, n2 in ((1, 3), (2, 4), (3, 6)):
        for q1 in range(1, 5):
            for q2 in range(1, 5):
                layers = [{"N40": n1, "q": q1}, {"N40": n2, "q": q2}]
                for h in (20, 28, 40 - n2):
                    out.append(make_case("K40", "A", layers, h))
    for ns in ((1, 3, 6), (2, 4, 8)):
        for qs in ((1, 1, 1), (2, 1, 1)):
            layers = [{"N40": n, "q": q} for n, q in zip(ns, qs)]
            for h in (20, 28, 40 - ns[-1]):
                out.append(make_case("K40", "A", layers, h))
    assert len(out) == 156 and len({c["case_id"] for c in out}) == 156
    return out


def score(row: dict):
    # Interval evidence is retained; this float is only a scheduling key.
    return (row["log_value_per_K2"], row["qsum"], row["h"], row["case_id"])


def route_b(a_rows: list[dict]) -> list[dict]:
    profiles = []
    for row in sorted(a_rows, key=score):
        key = tuple((x["N40"], x["q"]) for x in row["layers40"])
        if key not in profiles:
            profiles.append(key)
        if len(profiles) == 3:
            break
    if len(profiles) < 3:
        raise RuntimeError("Need three successful distinct A profiles before B")
    source = []
    for profile in profiles:
        candidates = [r for r in a_rows if tuple((x["N40"], x["q"]) for x in r["layers40"]) == profile]
        source.append(min(candidates, key=score))
    bases = [("control", [{"N40": 3, "q": 3}], 37, None)]
    bases += [("A", row["layers40"], row["h40"], row["case_id"]) for row in source]
    out = []
    for _, layers, h, src in bases:
        for shift in (0, 1, 2, 4, 8):
            out.append(make_case("K40", "B", layers, h, shift, source_case_id=src))
    assert len(out) == 20 and len({c["case_id"] for c in out}) == 20
    return out


def promote(rows: list[dict], stage: str, route: str, count: int) -> list[dict]:
    selected = sorted((r for r in rows if r["route"] == route and
                       (route != "B" or r["shift40"] > 0)), key=score)[:count]
    return [make_case(stage, route, r["layers40"], r["h40"], r["shift40"],
                      source_case_id=r["case_id"]) for r in selected]


def existing() -> dict[str, dict]:
    out = {}
    if INDEX.exists():
        for line in INDEX.read_text(encoding="utf-8").splitlines():
            if line.strip():
                row = json.loads(line)
                out[row["case_id"]] = row
    return out


def worker(case: dict, artifact: Path) -> dict:
    started = time.monotonic()
    result = parameters(case["s"], case["K"], 0, 0, case["h"],
                        {int(j): int(m) for j, m in case["zeros"].items()},
                        case["exponents"])
    ev = evaluate(result)
    full = record(result, ev, True)
    full.update({k: case[k] for k in ("case_id", "stage", "route", "r", "h40",
                                      "lam_ratio", "layers40", "basis_mode", "shift40", "g",
                                      "qsum", "source_case_id")})
    full["runtime"] = dict(python=sys.version, exact_script_sha256=digest(EXACT),
                           runner_script_sha256=digest(SCRIPT))
    full["seconds"] = round(time.monotonic() - started, 3)
    full["status"] = "ok"
    artifact.parent.mkdir(parents=True, exist_ok=True)
    temp = artifact.with_name(artifact.name + f".{os.getpid()}.tmp")
    with gzip.open(temp, "wt", encoding="utf-8") as f:
        json.dump(full, f, ensure_ascii=False, separators=(",", ":"))
    temp.replace(artifact)
    summary = {k: v for k, v in full.items() if k != "primitive_coefficients_ascending"}
    summary["artifact_path"] = str(artifact.relative_to(ROOT)).replace("\\", "/")
    summary["artifact_sha256"] = digest(artifact)
    return summary


def run_one(case: dict) -> dict:
    artifact = COEFF_DIR / (case["case_id"] + ".json.gz")
    command = [PYTHON, str(SCRIPT), "--worker-spec", json.dumps(case, separators=(",", ":")),
               "--worker-output", str(artifact)]
    started = time.monotonic()
    try:
        done = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                              timeout=DEADLINE, check=False)
        if done.returncode != 0:
            raise RuntimeError((done.stderr or done.stdout)[-1500:])
        row = json.loads(done.stdout)
        if row["case_id"] != case["case_id"]:
            raise AssertionError("Worker returned wrong case")
        return row
    except subprocess.TimeoutExpired:
        return dict(case_id=case["case_id"], stage=case["stage"], route=case["route"],
                    status="unresolved", error="subprocess_timeout_120s",
                    seconds=round(time.monotonic() - started, 3),
                    layers40=case["layers40"], h40=case["h40"], shift40=case["shift40"])
    except Exception as exc:
        return dict(case_id=case["case_id"], stage=case["stage"], route=case["route"],
                    status="unresolved", error=f"{type(exc).__name__}: {exc}",
                    seconds=round(time.monotonic() - started, 3),
                    layers40=case["layers40"], h40=case["h40"], shift40=case["shift40"])


def append(row: dict):
    INDEX.parent.mkdir(parents=True, exist_ok=True)
    with INDEX.open("a", encoding="utf-8") as f:
        f.write(json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n")
        f.flush()
        os.fsync(f.fileno())


def run_stage(name: str, cases: list[dict], known: dict, workers: int,
              limit_new: list[int]) -> bool:
    pending = [c for c in cases if known.get(c["case_id"], {}).get("status") != "ok"]
    if not pending:
        print(f"{name}: {len(cases)} complete from checkpoint", flush=True)
        return True
    pending = pending[:limit_new[0]]
    if not pending:
        return False
    print(f"{name}: {len(pending)} pending of {len(cases)}", flush=True)
    with ThreadPoolExecutor(max_workers=workers) as pool:
        future_map = {pool.submit(run_one, c): c for c in pending}
        for future in as_completed(future_map):
            row = future.result()
            append(row)
            known[row["case_id"]] = row
            limit_new[0] -= 1
            value = row.get("log_value_per_K2")
            print(f"{row['case_id']} {row['status']} rK={value}", flush=True)
    return all(known.get(c["case_id"], {}).get("status") == "ok" for c in cases)


def self_test():
    ordinary = parameters(7, 8, 1, 2, 4)
    explicit = parameters(7, 8, 1, 2, 4, exponents=list(range(4)))
    if ordinary["coeffs"] != explicit["coeffs"]:
        raise AssertionError("Default and explicit consecutive exponents differ")
    shifted = parameters(7, 8, 1, 2, 4, exponents=[0, 1, 3, 4])
    whole_shift = parameters(7, 8, 1, 2, 4, exponents=[2, 3, 4, 5])
    for item in (ordinary, shifted, whole_shift):
        for x in (0, 1, 3, 7):
            if item["delta"](x) != (item["A"] + x * item["B"]).det():
                raise AssertionError("Exact determinant mismatch")
    for bad in ([0, 0, 1, 2], [0, -1, 2, 3], [0, 1, 2]):
        try:
            parameters(7, 8, 1, 2, 4, exponents=bad)
        except ValueError:
            pass
        else:
            raise AssertionError("Invalid exponents were accepted")
    print("self-test: default/g0 coefficient identity and direct determinants passed", flush=True)


def compare_controls(known: dict):
    expected = {}
    for name in ("exact_baseline.json.gz", "exact_K80.json.gz", "exact_K80_s5.json.gz"):
        with gzip.open(VERIFY / name, "rt", encoding="utf-8") as f:
            for row in json.load(f):
                if row["q"] == 3:
                    expected[(row["s"], row["K"])] = row["coefficients_sha256"]
    for case in controls():
        row = known[case["case_id"]]
        key = (row["s"], row["K"])
        if row["coefficients_sha256"] != expected[key]:
            raise AssertionError(f"Control hash mismatch: {key}")
    print("four K40/K80 control hashes match prior artifacts", flush=True)


def compare_g0(b_cases: list[dict], known: dict):
    checked = 0
    for case in b_cases:
        if case["shift40"] != 0:
            continue
        row = known[case["case_id"]]
        source_id = case["source_case_id"]
        if source_id is None:
            source_id = make_case("K40", "C", [{"N40": 3, "q": 3}], 37)["case_id"]
        if row["coefficients_sha256"] != known[source_id]["coefficients_sha256"]:
            raise AssertionError("g0 source polynomial changed")
        checked += 1
    print(f"{checked} K40 g0 polynomial hashes match sources", flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--worker-spec")
    parser.add_argument("--worker-output")
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--limit-new", type=int, default=1000000,
                        help="Stop cleanly after this many new candidate attempts")
    args = parser.parse_args()
    if args.worker_spec:
        case = json.loads(args.worker_spec)
        print(json.dumps(worker(case, Path(args.worker_output)), ensure_ascii=False,
                         separators=(",", ":")))
        return
    if args.workers < 1 or args.workers > MAX_WORKERS:
        raise ValueError("At most two compute workers are allowed")
    self_test()
    known = existing()
    remaining = [args.limit_new]
    ctl = controls()
    if not run_stage("controls", ctl, known, args.workers, remaining):
        return
    compare_controls(known)
    a_cases = route_a()
    if not run_stage("A K40", a_cases, known, args.workers, remaining):
        return
    a_rows = [known[c["case_id"]] for c in a_cases]
    b_cases = route_b(a_rows)
    if not run_stage("B K40", b_cases, known, args.workers, remaining):
        return
    compare_g0(b_cases, known)
    b_rows = [known[c["case_id"]] for c in b_cases]
    promoted = promote(a_rows, "K80", "A", 4) + promote(b_rows, "K80", "B", 4)
    if not run_stage("A/B K80", promoted, known, args.workers, remaining):
        return
    high_rows = [known[c["case_id"]] for c in promoted]
    final = promote(high_rows, "K160", "A", 1) + promote(high_rows, "K160", "B", 1)
    if not run_stage("A/B K160", final, known, args.workers, remaining):
        return
    print("round-two search complete", flush=True)


if __name__ == "__main__":
    main()
