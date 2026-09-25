"""Exact inverse-normalized two-dimensional search, restricted to p=9, m=n, R=4.

The primitive pair lattice is used only to choose directions. Every reported
form is lifted back to an actual integral W in the saturated low-zeta kernel.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tmp/zeta7/exact_packages"))
sys.path.insert(0, str(ROOT / "missions/zeta9/round5/scripts"))
from flint import fmpq, fmpz_mat  # type: ignore
from weighted_forms import monomial_forms, integer_lattice, qp, rows_of, serializable  # type: ignore
from general_poles import score_value  # type: ignore

VERIFY = ROOT / "missions/zeta9/round6/verification"
OLD = ROOT / "missions/zeta9/round5/verification"


def qload(pair):
    return fmpq(int(pair[0]), int(pair[1]))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_old(n: int):
    path = OLD / f"weighted-p9-n{n}-m{n}-R4.json.gz"
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        data = json.load(stream)
    vectors = [[qload(x) for x in row] for row in data["raw_monomial_vectors"]]
    K = [[int(x) for x in row] for row in data["low_hnf"]["basis"]]
    return vectors, K, {
        "kind": "round5_archive", "path": str(path.relative_to(ROOT)).replace("\\", "/"),
        "sha256": digest(path), "lower_integer_matrix": data["lower_integer_matrix"],
        "lower_row_denominators": data["lower_row_denominators"],
        "low_hnf": data["low_hnf"], "full_rank": int(data["full_hnf"]["rank"]),
    }


def compute_new(n: int):
    form = monomial_forms(9, n, n, 4, check_points=True)
    lattice = integer_lattice(form)
    return form["raw_vectors"], lattice["low"]["basis"], {
        "kind": "recomputed_round6", "lower_integer_matrix": lattice["lower_rows"],
        "lower_row_denominators": lattice["lower_den"],
        "low_hnf": lattice["low"], "full_rank": lattice["full"]["rank"],
        "safe_degree_margin": form["safe_degree_margin"],
    }


def factor_small(v: int, bound: int):
    residue = abs(v)
    factors = []
    for p in range(2, bound + 1):
        if residue < p * p:
            break
        if any(p % d == 0 for d in range(2, math.isqrt(p) + 1)):
            continue
        if residue % p == 0:
            e = 0
            while residue % p == 0:
                residue //= p
                e += 1
            factors.append([p, e])
    if 1 < residue <= bound:
        factors.append([residue, 1])
        residue = 1
    return {"trial_bound": bound, "prime_powers": factors,
            "unresolved_cofactor": str(residue),
            "cofactor_sha256": hashlib.sha256(str(residue).encode()).hexdigest()}


def build_input(n: int):
    started = time.monotonic()
    vectors, K, provenance = read_old(n) if n in (12, 24, 48) else compute_new(n)
    if len(vectors) != 5 or any(len(row) != 5 for row in vectors) or len(K) != 2:
        raise AssertionError("Expected five columns and rank-two saturated kernel")
    F = []
    for w in K:
        full = [sum((w[r] * vectors[r][j] for r in range(5)), fmpq(0))
                for j in range(5)]
        if any(full[1:4]):
            raise AssertionError("Kernel did not kill all lower zeta coordinates")
        F.append([full[0], full[4]])
    Q = math.lcm(*(int(x.denom()) for row in F for x in row))
    J = [[int((Q * x).numer()) for x in row] for row in F]
    det = J[0][0] * J[1][1] - J[0][1] * J[1][0]
    if det == 0:
        raise AssertionError("Raw image has rank less than two")
    s1 = math.gcd(*(abs(x) for row in J for x in row))
    s2 = abs(det) // s1
    if s2 % s1 or s1 * s2 != abs(det):
        raise AssertionError("SNF invariant factors failed")
    snf = fmpz_mat(J).snf()
    if [abs(int(snf[i, i])) for i in range(2)] != [s1, s2]:
        raise AssertionError("FLINT SNF cross-check failed")
    src = Path(__file__)
    wf = ROOT / "missions/zeta9/round5/scripts/weighted_forms.py"
    gp = ROOT / "missions/zeta9/round2/scripts/general_poles.py"
    data = {
        "schema": "zeta9-round6-r4-input-v1", "case_id": f"p9-n{n}-m{n}-R4",
        "n": n, "p": 9, "m": n, "R": 4,
        "vector_order": ["B", "zeta3", "zeta5", "zeta7", "zeta9"],
        "W_order": ["u^0", "u^1", "u^2", "u^3", "u^4"], "u": "t(t+n)",
        "raw_monomial_vectors": vectors, "integer_W_basis_K_rows": K,
        "raw_image_F_rows_B_A": F, "common_denominator_Q": Q,
        "J_rows_B_A": J, "J_det": det, "SNF_s1": s1, "SNF_s2": s2,
        "small_prime_part": {"s1": factor_small(s1, max(1000, 2*n)),
                             "s2": factor_small(s2, max(1000, 2*n))},
        "provenance": provenance, "seconds": round(time.monotonic() - started, 3),
        "source_sha256": {"primitive_search": digest(src), "weighted_forms": digest(wf),
                          "general_poles": digest(gp)},
    }
    VERIFY.mkdir(parents=True, exist_ok=True)
    path = VERIFY / f"search-input-n{n}.json.gz"
    with gzip.open(path, "wt", encoding="utf-8", compresslevel=6) as stream:
        json.dump(serializable(data), stream, ensure_ascii=False, separators=(",", ":"))
    return {"n": n, "status": "ok", "seconds": data["seconds"],
            "artifact": str(path.relative_to(ROOT)).replace("\\", "/"),
            "artifact_sha256": digest(path), "Q_digits": len(str(Q)),
            "s1_digits": len(str(s1)), "s2_digits": len(str(s2))}


def load_input(n: int):
    path = VERIFY / f"search-input-n{n}.json.gz"
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        data = json.load(stream)
    return data, path


def inverse_rows(F):
    det = F[0][0] * F[1][1] - F[0][1] * F[1][0]
    if not det:
        raise ZeroDivisionError("Singular raw image")
    return [[F[1][1]/det, -F[0][1]/det],
            [-F[1][0]/det, F[0][0]/det]]


def multiply_2x5(left, right):
    return [[sum((left[i][k] * right[k][j] for k in range(2)), fmpq(0))
             for j in range(5)] for i in range(2)]


def primitive_direction(q):
    g = math.gcd(q[0], q[1])
    if not g:
        return None
    q = [x // g for x in q]
    if q[1] < 0 or (q[1] == 0 and q[0] < 0):
        q = [-x for x in q]
    return q


def run_search(n: int):
    started = time.monotonic()
    data, input_path = load_input(n)
    K = [[int(x) for x in row] for row in data["integer_W_basis_K_rows"]]
    F = [[qload(x) for x in row] for row in data["raw_image_F_rows_B_A"]]
    E = multiply_2x5(inverse_rows(F), K)
    weights = [n ** (2*r) for r in range(5)]
    D = math.lcm(*(int(x.denom()) for row in E for x in row))
    integral_weighted = [[int((D*E[i][j]*weights[j]).numer()) for j in range(5)]
                         for i in range(2)]
    reduced, transform = fmpz_mat(integral_weighted).lll(transform=True, gram="exact")
    T = rows_of(transform)
    if abs(int(transform.det())) != 1 or transform*fmpz_mat(integral_weighted) != reduced:
        raise AssertionError("Inverse weighted LLL transformation failed")
    generated = []
    seen = set()
    for a,b in itertools.product(range(-4,5), repeat=2):
        if math.gcd(a,b) != 1:
            continue
        before = [a*T[0][j]+b*T[1][j] for j in range(2)]
        q = primitive_direction(before)
        if q is None or tuple(q) in seen:
            continue
        seen.add(tuple(q))
        preimage = [sum((q[i]*E[i][j] for i in range(2)), fmpq(0)) for j in range(5)]
        norm_l1 = sum((abs(x)*weights[j] for j,x in enumerate(preimage)), fmpq(0))
        norm_sq = sum(((x*weights[j])**2 for j,x in enumerate(preimage)), fmpq(0))
        generated.append((norm_l1, norm_sq, q, [a,b], preimage, before,
                          q != before))
    generated.sort(key=lambda x:(x[0],x[1],max(abs(v) for v in x[2]),x[2]))
    # Fix the complete shortlist by exact arithmetic before any zeta evaluation.
    shortlist = [x for x in generated if x[2][1] != 0][:8]
    shortlist_pairs = [x[2] for x in shortlist]
    selected = []
    constants = []
    vectors = [[qload(x) for x in row] for row in data["raw_monomial_vectors"]]
    for norm_l1, norm_sq, q, combo, preimage, before, sign_flip in generated:
        denom = math.lcm(*(int(x.denom()) for x in preimage))
        integer = [int((denom*x).numer()) for x in preimage]
        content = math.gcd(*(abs(x) for x in integer))
        W = [x//content for x in integer]
        S = fmpq(denom, content)
        z = [S*sum((q[i]*inverse_rows(F)[i][j] for i in range(2)),fmpq(0))
             for j in range(2)]
        if any(x.denom()!=1 for x in z):
            raise AssertionError("Lift failed to land in original integer kernel")
        zint = [int(x.numer()) for x in z]
        if [sum(zint[i]*K[i][j] for i in range(2)) for j in range(5)] != W:
            raise AssertionError("Integer lift identity failed")
        raw = [sum((W[r]*vectors[r][j] for r in range(5)), fmpq(0)) for j in range(5)]
        if any(raw[1:4]) or raw[0] != S*q[0] or raw[4] != S*q[1]:
            raise AssertionError("Full coefficient lift identity failed")
        row = {"primitive_pair_B_A": q, "integer_W": W, "integer_K_coordinates": zint,
               "raw_pair_B_A": [raw[0],raw[4]], "primitive_multiplier_M": 1/S,
               "clearing_denominator": denom, "W_content_before_division": content,
               "inverse_preimage_qE": preimage, "qE_weighted_l1": norm_l1,
               "qE_weighted_sq": norm_sq, "LLL_combo": combo,
               "pair_before_sign_canonicalization": before,
               "sign_flip": sign_flip,
               "W_unweighted_l1": sum(abs(x) for x in W)}
        if q[1] == 0:
            constants.append(row)
            continue
        if q in shortlist_pairs:
            arb = score_value([9],[q[1]],q[0])
            row["arb"] = arb
            row["log_abs_per_n"] = arb["abs_log_value"]/n
            selected.append(row)
    output = {"schema": "zeta9-round6-inverse-normalized-search-v1",
              "n": n, "input": str(input_path.relative_to(ROOT)).replace("\\", "/"),
              "input_sha256": digest(input_path), "K_rows": K, "F_rows_B_A": F,
              "inverse_map_E_rows_qB_qA": E, "integer_weighted_E_common_D": D,
              "integer_weighted_E_rows": integral_weighted,
              "LLL_transform_unimodular_T": T,
              "LLL_reduced_integer_weighted_rows": rows_of(reduced),
              "enumeration": "primitive (a,b) in [-4,4]^2, canonical A>0 or A=0,B>0",
              "selection_exact_only": "first eight nonconstant directions by qE weighted L1, then squared L2 and pair tie-break; Arb happens only after shortlist fixed",
              "shortlist_pairs_pre_Arb_B_A": shortlist_pairs,
              "distinct_directions": len(generated), "selected": selected,
              "pure_constant_directions": constants,
              "seconds": round(time.monotonic()-started,3),
              "source_sha256": {"primitive_search": digest(Path(__file__))}}
    path = VERIFY / f"search-n{n}.json.gz"
    with gzip.open(path,"wt",encoding="utf-8",compresslevel=6) as stream:
        json.dump(serializable(output),stream,ensure_ascii=False,separators=(",",":"))
    return {"n":n,"status":"ok","seconds":output["seconds"],
            "selected_count":len(selected),"pure_constant_count":len(constants),
            "best_log_abs_per_n":min((x["log_abs_per_n"] for x in selected),default=None),
            "below_one":any(x["arb"]["below_one"] for x in selected),
            "artifact":str(path.relative_to(ROOT)).replace("\\","/"),
            "artifact_sha256":digest(path)}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True, choices=[12,24,48,96,192])
    parser.add_argument("--phase", choices=["input","search"], required=True)
    args=parser.parse_args()
    result=build_input(args.n) if args.phase=="input" else run_search(args.n)
    print(json.dumps(result,separators=(",",":")),flush=True)


if __name__=="__main__":
    main()
