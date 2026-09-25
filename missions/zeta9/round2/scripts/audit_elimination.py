"""Independent artifact, scale, cofactor, and signed-ball replay for round two."""
from __future__ import annotations

from fractions import Fraction
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"tmp/zeta7/exact_packages"))
from flint import arb,ctx,fmpz  # type: ignore

BASE=ROOT/"missions/zeta9/round2/verification"


def rows(name):
    out={}
    for line in (BASE/name).read_text(encoding="utf-8").splitlines():
        if line.strip():
            row=json.loads(line)
            out[row["case_id"]]=row
    return out


def rational(pair):
    return Fraction(int(pair[0]),int(pair[1]))


def ball(data):
    return arb(data["mid"],data["rad"])*arb(10)**data["exp"]


def signed_value(orders,vector,bits):
    constant=vector[0]
    with ctx.workprec(bits):
        # ζ(v)=1+(ζ(v)-1) is independent from the saved direct Horner sum.
        value=arb(fmpz(constant+sum(vector[1:])))
        for order,coefficient in reversed(list(zip(orders,vector[1:]))):
            value+=arb(fmpz(coefficient))*(arb(order).zeta()-1)
        return value


def sign_check(saved,orders,vector):
    bits=saved["arb_bits"]+128
    value=signed_value(orders,vector,bits)
    original=ball(saved["value_interval"])
    assert value.overlaps(original)
    sign=1 if value.lower()>0 else (-1 if value.upper()<0 else 0)
    assert sign==saved["sign"]!=0
    logabs=(value if sign>0 else -value).log()
    assert logabs.overlaps(ball(saved["abs_log_interval"]))
    below=bool(logabs.upper()<0)
    above=bool(logabs.lower()>0)
    assert below==saved["below_one"] and above==saved["above_one"]
    assert below or above
    return sign,below


def digest(values):
    return hashlib.sha256(",".join(map(str,values)).encode()).hexdigest()


def determinant(matrix):
    n=len(matrix)
    if n==0:
        return 1
    result=0
    for order in itertools.permutations(range(n)):
        inversions=sum(order[i]>order[j] for i in range(n) for j in range(i+1,n))
        term=math.prod(matrix[i][order[i]] for i in range(n))
        result+=(-1)**inversions*term
    return result


def audit():
    atom_rows=rows("elimination-atoms.jsonl")
    combo_rows=rows("elimination-results.jsonl")
    atoms={}
    atom_signs={"positive":0,"negative":0,"below_one":0,"above_one":0}
    for case,index in sorted(atom_rows.items()):
        assert index["status"]=="ok"
        path=ROOT/index["artifact_path"]
        assert hashlib.sha256(path.read_bytes()).hexdigest()==index["artifact_sha256"]
        with gzip.open(path,"rt",encoding="utf-8") as stream:
            row=json.load(stream)
        assert row["case_id"]==case
        p,n,m=row["p"],row["n"],row["m"]
        assert p in (3,5,7,9) and n%2==0 and m>=0
        assert row["d"]==9-p and row["b"]==10-p
        assert row["r"]==p*(n+1)-2-2*(10-p)*m>=0
        orders=list(range(12-p,10,2))
        assert orders==row["zeta_orders"]
        C=[(-1)**(m+k)*math.comb(n,k)**p
           *math.comb(k+m,m)**(10-p)*math.comb(n-k+m,m)**(10-p)
           for k in range(n+1)]
        G=math.gcd(*C)
        D=math.lcm(*range(1,n+m+1))
        assert G==int(row["G_residue_gcd"])
        assert D==int(row["D_lcm_n_plus_m"])
        certificate=rational(row["certificate_multiplier"])
        assert certificate==Fraction(D**9,G)
        raw=[rational(x) for x in row["raw_rational_vector"]]
        pre=[int(x) for x in row["preprimitive_integer_vector"]]
        assert [certificate*x for x in raw]==pre
        content=math.gcd(*pre)
        assert content==int(row["preprimitive_content"])>0
        primitive=[int(x) for x in row["primitive_integer_vector"]]
        assert primitive==[x//content for x in pre] and math.gcd(*primitive)==1
        assert rational(row["primitive_multiplier"])==certificate/content
        assert digest(primitive)==row["primitive_vector_sha256"]==index["primitive_vector_sha256"]
        sign,below=sign_check(row["signed_evaluation"],orders,primitive)
        assert sign==index["sign"] and below==index["below_one"]
        atom_signs["positive" if sign>0 else "negative"]+=1
        atom_signs["below_one" if below else "above_one"]+=1
        atoms[case]=row

    combo_signs={"positive":0,"negative":0,"below_one":0,"above_one":0}
    summary=[]
    for case,index in sorted(combo_rows.items()):
        assert index["status"]=="ok"
        path=ROOT/index["artifact_path"]
        assert hashlib.sha256(path.read_bytes()).hexdigest()==index["artifact_sha256"]
        with gzip.open(path,"rt",encoding="utf-8") as stream:
            row=json.load(stream)
        assert row["case_id"]==case and row["status"]=="ok"
        p,n=row["p"],row["n"]
        q=(p-1)//2
        assert row["q_forms"]==q and len(row["input_atom_artifacts"])==q
        vectors=[]
        for m,source in zip(row["m_values"],row["input_atom_artifacts"]):
            atom=atoms[f"p{p}-n{n}-m{m}"]
            source_path=ROOT/source["path"]
            assert hashlib.sha256(source_path.read_bytes()).hexdigest()==source["sha256"]
            assert source["primitive_vector_sha256"]==atom["primitive_vector_sha256"]
            vectors.append([int(x) for x in atom["primitive_integer_vector"]])
        assert vectors==[[int(x) for x in v] for v in row["input_primitive_vectors"]]
        low=[[v[j] for v in vectors] for j in range(1,q)]
        raw_weights=[(-1)**i*determinant([line[:i]+line[i+1:] for line in low])
                     for i in range(q)]
        assert raw_weights==[int(x) for x in row["raw_cofactor_weights"]]
        weight_content=math.gcd(*raw_weights)
        assert weight_content==int(row["weight_content"])>0
        weights=[x//weight_content for x in raw_weights]
        assert weights==[int(x) for x in row["weights"]]
        combined=[sum(weights[i]*vectors[i][j] for i in range(q)) for j in range(q+1)]
        assert combined==[int(x) for x in row["combined_vector"]]
        assert all(x==0 for x in combined[1:-1])
        content=math.gcd(combined[0],combined[-1])
        assert content==int(row["combination_content"])>0
        pair=[combined[-1]//content,combined[0]//content]
        assert pair==[int(x) for x in row["primitive_coefficients_A9_B"]]
        assert math.gcd(*pair)==1
        assert digest(pair)==row["coefficients_sha256"]==index["coefficients_sha256"]
        sign,below=sign_check(row["signed_evaluation"],[9],[pair[1],pair[0]])
        assert sign==index["sign"] and below==index["below_one"]
        combo_signs["positive" if sign>0 else "negative"]+=1
        combo_signs["below_one" if below else "above_one"]+=1
        summary.append({"case_id":case,"p":p,"n":n,"m_start":row["m_start"],
                        "profile_slot":row["profile_slot"],"sign":sign,
                        "below_one":below,"abs_log_per_n":index["abs_log_per_n"],
                        "coefficients_sha256":index["coefficients_sha256"]})
    output={"atom_count":len(atoms),"combination_count":len(summary),
            "atom_signs":atom_signs,"combination_signs":combo_signs,
            "all_exact_scales_and_cofactors_verified":True,
            "all_signed_arb_balls_rechecked":True,"combinations":summary}
    (BASE/"elimination-audit.json").write_text(json.dumps(output,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:v for k,v in output.items() if k!="combinations"}))


if __name__=="__main__":
    audit()
