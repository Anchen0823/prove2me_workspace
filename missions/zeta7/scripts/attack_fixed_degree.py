"""Resumable 36-case fixed-degree exact search using the infinity rank boundary."""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from exact_hankel import ROOT


VERIFY = ROOT / "missions/zeta7/verification"
INDEX = VERIFY / "round2-fixed-degree.jsonl"
MANIFEST = VERIFY / "round2-fixed-degree-manifest.json"
COEFF_DIR = VERIFY / "round2-fixed-degree-coeff"
WORKER = Path(__file__).with_name("attack_round2.py")
TIMEOUT = 120


def sha256(path: Path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def candidates():
    layouts = [((1, 1), (3, 1)), ((2, 1), (4, 1)),
               ((1, 1), (3, 1), (6, 1))]
    cases = []
    for K in (40, 80):
        scale = K // 40
        for layout in layouts:
            layers40 = [dict(N40=n, q=q) for n, q in layout]
            qsum = sum(q for _, q in layout)
            d = 2 * sum(n * q for n, q in layout) * scale
            zeros = {j: sum(q for n, q in layout if j <= n * scale)
                     for j in range(1, layout[-1][0] * scale + 1)}
            r = K - len(zeros)
            for shift40 in (0, 1):
                g = shift40 * scale
                L = K - d - 4 - 2 * g
                for m in (1, 3, 5):
                    numerator = K - d - 2 * g - 3 + m
                    assert numerator % 2 == 0
                    h = numerator // 2
                    assert 0 < h <= r and h - 1 <= L <= 2 * h - 2
                    assert 2 * h - 1 - L == m
                    label = "_".join(f"n{n}q{q}" for n, q in layout)
                    case_id = f"K{K}-F-s7-{label}-g{shift40}-m{m}"
                    cases.append(dict(case_id=case_id, stage=f"K{K}", route="F",
                                      s=7, K=K, h=h, r=r, h40=None,
                                      lam_ratio=f"{h}/{K}", layers40=layers40,
                                      shift40=shift40, g=g, qsum=qsum,
                                      basis_mode="whole_shift", zeros=zeros,
                                      exponents=list(range(g, g + h)),
                                      source_case_id=None,
                                      target_degree=m, infinity_threshold_L=L,
                                      limiting_lambda_numerator=20 - sum(n*q for n,q in layout) - shift40,
                                      limiting_lambda_denominator=40))
    assert len(cases) == 36 and len({c["case_id"] for c in cases}) == 36
    return cases


def load_known():
    if not INDEX.exists():
        return {}
    rows = [json.loads(line) for line in INDEX.read_text(encoding="utf-8").splitlines() if line]
    return {r["case_id"]: r for r in rows}


def append(row):
    INDEX.parent.mkdir(parents=True, exist_ok=True)
    with INDEX.open("a", encoding="utf-8") as f:
        f.write(json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n")
        f.flush()
        os.fsync(f.fileno())


def run_one(case):
    artifact = COEFF_DIR / f"{case['case_id']}.json.gz"
    command = [sys.executable, str(WORKER), "--worker-spec",
               json.dumps(case, separators=(",", ":")), "--worker-output", str(artifact)]
    start = time.monotonic()
    try:
        done = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                              timeout=TIMEOUT, check=False)
        if done.returncode:
            raise RuntimeError((done.stderr or done.stdout)[-1500:])
        row = json.loads(done.stdout)
        assert row["case_id"] == case["case_id"]
        assert row["degree"] == row["B_rank"] == case["target_degree"]
        assert row["infinity_threshold_L"] == case["infinity_threshold_L"]
        row["target_degree"] = case["target_degree"]
        row["limiting_lambda_numerator"] = case["limiting_lambda_numerator"]
        row["limiting_lambda_denominator"] = case["limiting_lambda_denominator"]
        row["fixed_runner_sha256"] = sha256(Path(__file__))
        return row
    except subprocess.TimeoutExpired:
        error = "subprocess_timeout_120s"
    except Exception as exc:
        error = f"{type(exc).__name__}: {exc}"
    return dict(case_id=case["case_id"], stage=case["stage"], route="F",
                status="unresolved", error=error,
                seconds=round(time.monotonic() - start, 3),
                target_degree=case["target_degree"],
                limiting_lambda_numerator=case["limiting_lambda_numerator"],
                limiting_lambda_denominator=40)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--limit-new", type=int, default=36)
    args = parser.parse_args()
    if not 1 <= args.workers <= 2:
        raise ValueError("At most two compute workers")
    cases = candidates()
    VERIFY.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text(json.dumps(cases, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    known = load_known()
    pending = [c for c in cases if known.get(c["case_id"], {}).get("status") != "ok"][:args.limit_new]
    print(f"fixed-degree: {len(pending)} pending, {len(cases)} total", flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, c): c for c in pending}
        for future in as_completed(futures):
            row = future.result()
            append(row)
            print(f"{row['case_id']} {row['status']} rK={row.get('log_value_per_K2')}", flush=True)
    final = load_known()
    print(f"fixed-degree complete: {sum(final.get(c['case_id'],{}).get('status')=='ok' for c in cases)}/36",
          flush=True)


if __name__ == "__main__":
    sys.set_int_max_str_digits(0)
    main()
