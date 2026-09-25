"""Fixed prime-window congruence scan for five archived zeta(9) scales."""
from __future__ import annotations

import argparse
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(Path(__file__).resolve().parent))
from modulus_scan import (BASE,R6,digest,gauss,gram,log_bound_ball,
                          matmul_2,read_input,serializable)  # type: ignore

OUT=ROOT/"missions/zeta9/round7/verification/prime-window-scan.json"


def one_case(n,audit):
    started=time.monotonic()
    inp,path=read_input(n)
    smith=audit["smith_certificate"]
    K=[[int(x) for x in row] for row in inp["integer_W_basis_K_rows"]]
    J=[[int(x) for x in row] for row in inp["J_rows_B_A"]]
    U=[[int(x) for x in row] for row in smith["U"]]
    V=[[int(x) for x in row] for row in smith["V"]]
    D=int(inp["common_denominator_Q"])
    s1,s2,N=[int(smith[key]) for key in ("s1","s2","N")]
    assert audit["input_sha256"]==digest(path)
    assert matmul_2(matmul_2(U,J),V)==[[s1,0],[0,s2]]
    assert s2==s1*N and s1==1
    factors=[[int(p),int(e)] for p,e in
             inp["small_prime_part"]["s2"]["prime_powers"]]
    assert int(inp["small_prime_part"]["s2"]["unresolved_cofactor"])==1
    UK=matmul_2(U,K)
    modes=[]
    for mode,weights in (("unweighted",[1]*5),
                         ("n2r",[n**(2*r) for r in range(5)])):
        kg=gram(K,weights)
        delta_squared=kg[0]*kg[2]-kg[1]**2
        windows=[]
        for c in (2,3,4):
            selected=[[p,min(e,2)] for p,e in factors if p*c>n and p<=n]
            g=1
            for p,e in selected:
                g*=p**e
            assert N%g==0
            basis=[[g*x for x in UK[0]],list(UK[1])]
            initial=gram(basis,weights)
            H,reduced,steps=gauss(initial)
            reduced_rows=matmul_2(H,basis)
            assert tuple(reduced)==gram(reduced_rows,weights)
            assert reduced[0]*reduced[2]-reduced[1]**2==g*g*delta_squared
            mu_squared=reduced[0]
            bound_squared=Fraction(4*D*D*delta_squared,
                                   3*s1*s1*mu_squared)
            windows.append({"c":c,"prime_condition":f"n/{c} < p <= n",
                            "selected_prime_powers":selected,
                            "g":g,"N_over_g":N//g,
                            "basis_rows_diag_g_1_UK":basis,
                            "initial_gram_A_B_C":list(initial),
                            "gauss_unimodular_H":H,
                            "gauss_reduced_rows":reduced_rows,
                            "gauss_reduced_gram_A_B_C":reduced,
                            "gauss_steps":steps,"mu1_squared":mu_squared,
                            "deltaK_squared":delta_squared,
                            "lambda2_upper_squared_numerator_denominator":
                               [bound_squared.numerator,bound_squared.denominator],
                            "log_lambda2_upper_per_n":log_bound_ball(
                                n,D,s1,delta_squared,mu_squared)})
        modes.append({"mode":mode,"weights":weights,"windows":windows})
    return {"n":n,"input_sha256":digest(path),"smith_audit_sha256":digest(BASE),
            "D":D,"s1":s1,"N":N,"K_rows":K,"smith_U":U,"smith_V":V,
            "N_complete_factorization":factors,"modes":modes,
            "seconds":round(time.monotonic()-started,3)}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--n",type=int,nargs="*",default=[12,24,48,96,192])
    parser.add_argument("--force",action="store_true")
    args=parser.parse_args()
    if any(n not in (12,24,48,96,192) for n in args.n):
        parser.error("Only the five existing n values are allowed")
    audit=json.loads(BASE.read_text(encoding="utf-8"))
    by_n={int(row["n"]):row for row in audit["cases"]}
    existing={}
    if OUT.exists() and not args.force:
        existing={int(row["n"]):row for row in
                  json.loads(OUT.read_text(encoding="utf-8"))["cases"]}
    start=time.monotonic()
    for n in args.n:
        if n in existing:
            continue
        row=one_case(n,by_n[n])
        if row["seconds"]>120:
            raise TimeoutError(f"n={n} exceeded 120 s")
        existing[n]=serializable(row)
        output={"schema":"zeta9-round7-fixed-prime-window-v1",
                "scope":"finite exact n=12,24,48,96,192; c=2,3,4 only; no zeta values",
                "cases":[existing[k] for k in sorted(existing)],
                "source_sha256":{"prime_window_scan":digest(Path(__file__)),
                                 "modulus_scan":digest(Path(__file__).with_name(
                                     "modulus_scan.py")),"smith_audit":digest(BASE)},
                "elapsed_seconds":round(time.monotonic()-start,3)}
        OUT.parent.mkdir(parents=True,exist_ok=True)
        OUT.write_text(json.dumps(output,ensure_ascii=False,indent=2),encoding="utf-8")
        print(json.dumps({"n":n,"status":"ok","seconds":row["seconds"],
                          "weighted_10_564":[x["log_lambda2_upper_per_n"]
                            ["threshold_comparisons"]["10.564"] for x in row["modes"][1]
                            ["windows"]]},ensure_ascii=False),flush=True)


if __name__=="__main__":
    main()
