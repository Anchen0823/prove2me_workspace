"""Exact rational-shift zeta(9) forms; finite evidence, not a proof of irrationality.

All pole and shift calculations use python-flint rationals.  The only Arb
operation is the final, signed interval evaluation of the integer linear form.
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
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tmp/zeta7/exact_packages"))
from flint import arb, ctx, fmpq, fmpz  # type: ignore

VERIFY = ROOT / "missions/zeta9/round3/verification"


def validate(D: int, n: int, m: int) -> int:
    if D not in (6, 8) or n < 2 or n % 2 or m < 0:
        raise ValueError("Require D in {6,8}, positive even n, and m>=0")
    slack = (10-D)*n+7-2*D*m
    if slack < 0:
        raise ValueError("Require 2Dm <= (10-D)n+7")
    return slack


def qp(x: fmpq) -> list[str]:
    return [str(x.numer()), str(x.denom())]


def iv(x: arb, digits: int = 45) -> dict:
    mid, rad, exp = x.mid_rad_10exp(digits)
    return {"mid": str(mid), "rad": str(rad), "exp": int(exp)}


def signed_arb(A: int, B: int) -> dict:
    bits = max(256, max(abs(A).bit_length(), abs(B).bit_length())+400)
    for _ in range(9):
        with ctx.workprec(bits):
            value = arb(fmpz(A))*arb(9).zeta()+arb(fmpz(B))
            sign = 1 if value.lower() > 0 else (-1 if value.upper() < 0 else 0)
            if sign and value.rel_accuracy_bits() >= 80:
                logabs = (value if sign > 0 else -value).log()
                return {"sign": sign, "value_interval": iv(value),
                        "log_abs_interval": iv(logabs),
                        "log_abs": float(logabs),
                        "below_one": bool(logabs.upper() < 0),
                        "above_one": bool(logabs.lower() > 0),
                        "arb_bits": bits,
                        "relative_accuracy_bits": value.rel_accuracy_bits()}
        bits *= 2
    raise ArithmeticError("Arb could not certify a nonzero signed value")


def retained_ell(D: int, n: int, m: int) -> list[int]:
    """Cancel only ell=0,D,...,Dn; keep exterior integral numerator factors."""
    return [ell for ell in range(-D*m, D*(n+m)+1)
            if not (ell % D == 0 and 0 <= ell//D <= n)]


def fixed_weights(D: int) -> tuple[list[int], list[int], int]:
    divisors = [d for d in range(1, D+1) if D % d == 0]
    if len(divisors) != 4:
        raise AssertionError("Expected exactly four divisors")
    def det3(mat: list[list[int]]) -> int:
        return (mat[0][0]*(mat[1][1]*mat[2][2]-mat[1][2]*mat[2][1])
                -mat[0][1]*(mat[1][0]*mat[2][2]-mat[1][2]*mat[2][0])
                +mat[0][2]*(mat[1][0]*mat[2][1]-mat[1][1]*mat[2][0]))
    rows = [[d**s for d in divisors] for s in (3,5,7)]
    raw = [(-1)**j*det3([[v for k,v in enumerate(row) if k != j]
                         for row in rows]) for j in range(4)]
    gcd = math.gcd(*raw)
    weights = [v//gcd for v in raw]
    if weights[-1] < 0:
        weights = [-v for v in weights]
    if any(sum(w*d**s for w,d in zip(weights,divisors)) for s in (3,5,7)):
        raise AssertionError("Fixed weights did not eliminate low zeta orders")
    kappa = sum(w*d**9 for w,d in zip(weights,divisors))
    if kappa <= 0:
        raise AssertionError("Expected positive zeta(9) multiplier")
    return divisors, weights, kappa


def rational_model(D: int, n: int, m: int, check_points: bool = False) -> dict:
    slack = validate(D,n,m)
    ell = retained_ell(D,n,m)
    expected = (D-1)*n+2*D*m
    if len(ell) != expected:
        raise AssertionError("Incorrect numerator factor count")
    F = fmpq(math.factorial(n)**(10-D),math.factorial(m)**(2*D))
    poles = {s: [] for s in range(1,10)}
    for j in range(n+1):
        C = (F*fmpq(math.factorial(D*(j+m))
                    *math.factorial(D*(n+m-j)),D**(D*(n+2*m)))
             / (math.factorial(j)*math.factorial(n-j))**10)
        sums = [fmpq(0)]*9
        for v in range(1,9):
            numerator = sum((fmpq(D, e-D*j)**v for e in ell),fmpq(0))
            denominator = 9*sum((fmpq(1,i-j)**v for i in range(n+1)
                                 if i != j),fmpq(0))
            sums[v] = numerator-denominator
        series = [fmpq(1)]
        for r in range(1,9):
            series.append(sum(((-1)**(v+1)*sums[v]*series[r-v]
                               for v in range(1,r+1)),fmpq(0))/r)
        for r,coefficient in enumerate(series):
            poles[9-r].append(C*coefficient)
    rho = {s: sum(poles[s],fmpq(0)) for s in range(1,10)}
    if any(rho[s] for s in (1,2,4,6,8)):
        raise AssertionError("Reflection/decay cancellations failed")
    if any(poles[s][n-j] != (-1)**(s+1)*poles[s][j]
           for s in range(1,10) for j in range(n+1)):
        raise AssertionError("Reflection coefficient identity failed")
    if rho[9] <= 0:
        raise AssertionError("Highest residue must be positive")

    B_a = []
    for a in range(1,D+1):
        harmonic = {s:[fmpq(0)] for s in range(1,10)}
        for j in range(1,n+1):
            for s in range(1,10):
                harmonic[s].append(harmonic[s][-1]+fmpq(D,D*(j-1)+a)**s)
        B_a.append(-sum((poles[s][j]*harmonic[s][j]
                         for s in range(1,10) for j in range(n+1)),fmpq(0)))

    divisors, weights, kappa = fixed_weights(D)
    B_d = [sum((B_a[a*D//d-1] for a in range(1,d+1)),fmpq(0))
           for d in divisors]
    A = rho[9]*kappa
    B = sum((w*b for w,b in zip(weights,B_d)),fmpq(0))
    if A <= 0:
        raise AssertionError("Target coefficient vanished")
    denominator = math.lcm(int(A.denom()),int(B.denom()))
    pres = [int((A*denominator).numer()),int((B*denominator).numer())]
    content = math.gcd(*pres)
    primitive = [v//content for v in pres]
    if math.gcd(*primitive) != 1 or primitive[0] <= 0:
        raise AssertionError("Primitive normalization failed")

    if check_points:
        for t in (fmpq(1,2),fmpq(m+1),fmpq(n+m+2)):
            direct = F*math.prod((t+fmpq(e,D) for e in ell),start=fmpq(1))
            direct /= math.prod(((t+j)**9 for j in range(n+1)),start=fmpq(1))
            partial = sum((poles[s][j]/(t+j)**s
                           for s in range(1,10) for j in range(n+1)),fmpq(0))
            if direct != partial:
                raise AssertionError("Exact rational/PF check failed")
    return {"D":D,"n":n,"m":m,"slack":slack,"retained_ell":ell,
            "F":F,"poles":poles,"rho":rho,"B_a":B_a,
            "divisors":divisors,"weights":weights,"kappa":kappa,
            "B_d":B_d,"raw_A":A,"raw_B":B,
            "raw_denominator":denominator,"preprimitive":pres,
            "content":content,"primitive":primitive,
            "primitive_multiplier":fmpq(denominator,content)}


def case_id(D:int,n:int,m:int) -> str:
    return f"D{D}-n{n}-m{m}"


def save_model(model:dict,elapsed:float) -> dict:
    D,n,m = model["D"],model["n"],model["m"]
    case = case_id(D,n,m)
    scored = signed_arb(*model["primitive"])
    script_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    pair_sha = hashlib.sha256(",".join(map(str,model["primitive"])).encode()).hexdigest()
    pole_data = [[qp(model["poles"][s][j]) for s in range(1,10)]
                 for j in range(n+1)]
    artifact = {"case_id":case,"definition":"shift-rational-fixed-weights-v1",
                "D":D,"n":n,"m":m,"slack":model["slack"],
                "retained_ell":model["retained_ell"],"F":qp(model["F"]),
                "pole_coefficients_j_by_s1_to9":pole_data,
                "rho_s1_to9":[qp(model["rho"][s]) for s in range(1,10)],
                "B_a_a1_toD":[qp(v) for v in model["B_a"]],
                "divisors":model["divisors"],"weights":model["weights"],
                "kappa9":model["kappa"],"B_d":[qp(v) for v in model["B_d"]],
                "raw_A_B":[qp(model["raw_A"]),qp(model["raw_B"])],
                "raw_denominator":str(model["raw_denominator"]),
                "preprimitive_A_B":[str(v) for v in model["preprimitive"]],
                "content":str(model["content"]),
                "primitive_multiplier":qp(model["primitive_multiplier"]),
                "primitive_A_B":[str(v) for v in model["primitive"]],
                "primitive_sha256":pair_sha,"script_sha256":script_sha,
                "arb":scored,"elapsed_seconds":elapsed}
    VERIFY.mkdir(parents=True,exist_ok=True)
    path=VERIFY/f"shift-{case}.json.gz"
    with gzip.open(path,"wt",encoding="utf-8",compresslevel=6) as stream:
        json.dump(artifact,stream,ensure_ascii=False,separators=(",",":"))
    return {"case_id":case,"status":"ok","D":D,"n":n,"m":m,
            "slack":model["slack"],"artifact":str(path.relative_to(ROOT)),
            "primitive_sha256":pair_sha,"script_sha256":script_sha,
            "primitive_A_digits":len(str(model["primitive"][0])),
            "primitive_B_digits":len(str(abs(model["primitive"][1]))),
            "primitive_multiplier":qp(model["primitive_multiplier"]),
            "sign":scored["sign"],"below_one":scored["below_one"],
            "above_one":scored["above_one"],
            "log_abs":scored["log_abs"],
            "log_abs_per_n":scored["log_abs"]/n,
            "arb_bits":scored["arb_bits"],"seconds":elapsed}


def self_test() -> dict:
    six=fixed_weights(6)
    eight=fixed_weights(8)
    assert six == ([1,2,3,6],[-7776,1701,-224,1],6531840)
    assert eight == ([1,2,4,8],[-32768,5376,-168,1],92897280)
    for D,n,m in ((6,2,0),(6,2,1),(8,2,0),(8,6,1)):
        rational_model(D,n,m,check_points=True)
    negative=signed_arb(-1,0)
    assert negative["sign"] == -1
    return {"status":"ok","small_cases":4,"D6_weights":six,
            "D8_weights":eight,"negative_arb_sign":negative["sign"]}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--D",type=int)
    parser.add_argument("--n",type=int)
    parser.add_argument("--m",type=int)
    parser.add_argument("--self-test",action="store_true")
    parser.add_argument("--check-points",action="store_true")
    args=parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(),ensure_ascii=False))
        return
    if None in (args.D,args.n,args.m):
        parser.error("--D, --n, and --m are required")
    start=time.monotonic()
    model=rational_model(args.D,args.n,args.m,check_points=args.check_points)
    result=save_model(model,time.monotonic()-start)
    print(json.dumps(result,ensure_ascii=False,separators=(",",":")),flush=True)


if __name__=="__main__":
    main()
