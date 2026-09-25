"""Read-only exact re-audit of archived Round6 matrices and lifted candidates."""
from __future__ import annotations

import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"tmp/zeta7/exact_packages"))
from flint import fmpq,fmpz_mat  # type: ignore

VERIFY=ROOT/"missions/zeta9/round6/verification"


def read(path):
    with gzip.open(path,"rt",encoding="utf-8") as stream:
        return json.load(stream)


def q(value):
    return fmpq(int(value[0]),int(value[1]))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run():
    rows=[]
    seen={}
    for n in (12,24,48,96,192):
        inp_path=VERIFY/f"search-input-n{n}.json.gz"
        out_path=VERIFY/f"search-n{n}.json.gz"
        inp,out=read(inp_path),read(out_path)
        assert out["input_sha256"]==digest(inp_path)
        V=[[q(x) for x in row] for row in inp["raw_monomial_vectors"]]
        K=[[int(x) for x in row] for row in inp["integer_W_basis_K_rows"]]
        F=[[q(x) for x in row] for row in inp["raw_image_F_rows_B_A"]]
        Q=int(inp["common_denominator_Q"])
        J=[[int(x) for x in row] for row in inp["J_rows_B_A"]]
        assert [[Q*x for x in row] for row in F]==J
        assert [abs(int(fmpz_mat(J).snf()[i,i])) for i in range(2)]==[
            int(inp["SNF_s1"]),int(inp["SNF_s2"])]
        assert abs(int(inp["J_det"]))==int(inp["SNF_s1"])*int(inp["SNF_s2"])
        for k,w in enumerate(K):
            projected=[sum((w[r]*V[r][j] for r in range(5)),fmpq(0))
                       for j in range(5)]
            assert projected[1:4]==[fmpq(0)]*3
            assert [projected[0],projected[4]]==F[k]
        E=[[q(x) for x in row] for row in out["inverse_map_E_rows_qB_qA"]]
        for k in range(2):
            assert [sum((E[k][r]*V[r][j] for r in range(5)),fmpq(0))
                    for j in range(5)]==([fmpq(1),fmpq(0),fmpq(0),fmpq(0),fmpq(0)]
                                    if k==0 else
                                    [fmpq(0),fmpq(0),fmpq(0),fmpq(0),fmpq(1)])
        D=int(out["integer_weighted_E_common_D"])
        weighted=fmpz_mat([[int((D*E[i][r]*n**(2*r)).numer()) for r in range(5)]
                           for i in range(2)])
        T=fmpz_mat([[int(x) for x in row] for row in out["LLL_transform_unimodular_T"]])
        assert abs(int(T.det()))==1
        assert T*weighted==fmpz_mat([[int(x) for x in row]
                                    for row in out["LLL_reduced_integer_weighted_rows"]])
        shortlist=[[int(x) for x in pair] for pair in out["shortlist_pairs_pre_Arb_B_A"]]
        assert shortlist==[[int(x) for x in row["primitive_pair_B_A"]]
                           for row in out["selected"]]
        for candidate in out["selected"]+out["pure_constant_directions"]:
            pair=[int(x) for x in candidate["primitive_pair_B_A"]]
            W=[int(x) for x in candidate["integer_W"]]
            z=[int(x) for x in candidate["integer_K_coordinates"]]
            S=1/q(candidate["primitive_multiplier_M"])
            assert math.gcd(*pair)==1 and math.gcd(*W)==1
            assert W==[sum(z[i]*K[i][r] for i in range(2)) for r in range(5)]
            whole=[sum((W[r]*V[r][j] for r in range(5)),fmpq(0))
                   for j in range(5)]
            assert whole==[S*pair[0],0,0,0,S*pair[1]]
            before=[int(x) for x in candidate["pair_before_sign_canonicalization"]]
            assert pair==([-x for x in before] if candidate["sign_flip"] else before)
            combo=[int(x) for x in candidate["LLL_combo"]]
            assert before==[sum(combo[i]*int(T[i,j]) for i in range(2)) for j in range(2)]
            key=tuple(pair)
            seen.setdefault(key,[]).append(n)
        rows.append({"n":n,"input_sha256":digest(inp_path),"search_sha256":digest(out_path),
                     "SNF_s1":inp["SNF_s1"],"SNF_s2_digits":len(inp["SNF_s2"]),
                     "selected_count":len(out["selected"]),
                     "constant_count":len(out["pure_constant_directions"]),
                     "best_log_abs_per_n":min((x["log_abs_per_n"] for x in out["selected"]),
                                              default=None),
                     "all_selected_below_one":all(x["arb"]["below_one"]
                                                  for x in out["selected"])})
    repeated={str(key):ns for key,ns in seen.items() if len(set(ns))>1}
    result={"status":"pass","cases":rows,"selected_total":sum(x["selected_count"] for x in rows),
            "cross_n_repeated_primitive_pairs":repeated,
            "audit_source_sha256":digest(Path(__file__))}
    path=VERIFY/"search-audit.json"
    path.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False))


if __name__=="__main__":
    run()
