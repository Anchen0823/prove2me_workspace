"""Recheck saved odd-zeta linear forms, integer scales and signed Arb balls."""
from __future__ import annotations

from fractions import Fraction
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"tmp/zeta7/exact_packages"))
from flint import arb,ctx,fmpz  # type: ignore

VERIFY=ROOT/"missions/zeta9/verification"
INDEX=VERIFY/"linear-results.jsonl"
OUTPUT=VERIFY/"linear-audit.json"


def rat(pair):
    return Fraction(int(pair[0]),int(pair[1]))


def saved_ball(data):
    return arb(data["mid"],data["rad"])*arb(10)**data["exp"]


def main():
    latest={}
    for line in INDEX.read_text(encoding="utf-8").splitlines():
        if line.strip():
            row=json.loads(line)
            latest[row["case_id"]]=row
    verified=[]
    for case,row in sorted(latest.items()):
        if row["status"]!="ok":
            continue
        path=ROOT/row["artifact_path"]
        assert hashlib.sha256(path.read_bytes()).hexdigest()==row["artifact_sha256"]
        with gzip.open(path,"rt",encoding="utf-8") as stream:
            full=json.load(stream)
        assert full["case_id"]==case
        s,n,m=full["s"],full["n"],full["m"]
        assert n%2==0 and s%2==1 and s>=5
        assert full["r"]==3*n+1-2*(s-2)*m>=0
        assert int(full["d_lcm_n_plus_m"])==math.lcm(*range(1,n+m+1))
        C=[(-1)**(m+k)*math.comb(n,k)**3
           *math.comb(k+m,m)**(s-2)
           *math.comb(n-k+m,m)**(s-2) for k in range(n+1)]
        assert int(full["G_residue_gcd"])==math.gcd(*C)
        A,B=rat(full["A_zeta_rational"]),rat(full["B_constant_rational"])
        cert=rat(full["certificate_multiplier"])
        assert cert==Fraction(2*int(full["d_lcm_n_plus_m"])**s,
                              int(full["G_residue_gcd"]))
        pre=[int(x) for x in full["preprimitive_integer_coefficients"]]
        assert [cert*A,cert*B]==pre
        content=int(full["preprimitive_content"])
        assert content==math.gcd(*pre)>0
        a,b=[int(x) for x in full["primitive_integer_coefficients"]]
        assert (a,b)==(pre[0]//content,pre[1]//content)
        assert math.gcd(a,b)==1
        scale=rat(full["primitive_multiplier"])
        assert scale==cert/content and [scale*A,scale*B]==[a,b]
        assert cert/scale==content
        digest=hashlib.sha256(f"{a},{b}".encode()).hexdigest()
        assert digest==full["coefficients_sha256"]==row["coefficients_sha256"]
        assert row["runtime"]==full["runtime"]
        bits=max(512,full["signed_evaluation"]["arb_bits"]+128)
        with ctx.workprec(bits):
            # Grouping differs from the saved direct a*zeta+b evaluation.
            value=arb(fmpz(a))*(arb(s).zeta()+arb(fmpz(b))/arb(fmpz(a)))
            saved=saved_ball(full["signed_evaluation"]["value_interval"])
            assert value.overlaps(saved)
            sign=1 if value.lower()>0 else (-1 if value.upper()<0 else 0)
            assert sign==row["sign"]==full["signed_evaluation"]["sign"]
            assert sign!=0
            logabs=(value if sign>0 else -value).log()
            assert logabs.overlaps(saved_ball(full["signed_evaluation"]["abs_log_interval"]))
            below=bool(logabs.upper()<0)
            above=bool(logabs.lower()>0)
            assert below==row["below_one"]==full["signed_evaluation"]["below_one"]
            assert above==row["above_one"]==full["signed_evaluation"]["above_one"]
            assert below or above
        verified.append({"case_id":case,"s":s,"n":n,"m":m,"r":full["r"],
                         "sign":sign,"above_one":above,"below_one":below,
                         "certificate_to_primitive_gap":str(content),
                         "gap_log_per_n":math.log(content)/n,
                         "coefficients_sha256":digest,
                         "certificate_and_primitive_scales_exact":True,
                         "signed_arb_recheck":True})
    summary={"verified":len(verified),
             "above_one":sum(x["above_one"] for x in verified),
             "below_one":sum(x["below_one"] for x in verified),
             "positive":sum(x["sign"]>0 for x in verified),
             "negative":sum(x["sign"]<0 for x in verified),
             "records":verified}
    OUTPUT.write_text(json.dumps(summary,indent=2,ensure_ascii=False)+"\n",encoding="utf-8")
    print(json.dumps({k:v for k,v in summary.items() if k!="records"},ensure_ascii=False))


if __name__=="__main__":
    main()
