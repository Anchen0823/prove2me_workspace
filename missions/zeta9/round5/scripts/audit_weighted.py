"""Independent exact archive audit of invariant-polynomial fifth-round blocks."""
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
from flint import arb,ctx,fmpq,fmpz,fmpz_mat  # type: ignore

VERIFY=ROOT/"missions/zeta9/round5/verification"
INDEX=VERIFY/"weighted-results.jsonl"


def q(pair:list[str]) -> fmpq:
    return fmpq(int(pair[0]),int(pair[1]))


def ints(values:list) -> list[int]:
    return [int(v) for v in values]


def matrix(rows:list[list[int]],cols:int) -> fmpz_mat:
    return fmpz_mat(rows) if rows else fmpz_mat(0,cols)


def sha(values:list[int]) -> str:
    return hashlib.sha256(",".join(map(str,values)).encode()).hexdigest()


def pole_direct(p:int,n:int,m:int,t:fmpq) -> fmpq:
    b=10-p
    pref=fmpq(math.factorial(n)**p,math.factorial(m)**(2*b))
    num=(math.prod((t-j for j in range(1,m+1)),start=fmpq(1))
         *math.prod((t+n+j for j in range(1,m+1)),start=fmpq(1)))**b
    den=math.prod(((t+j)**p for j in range(n+1)),start=fmpq(1))
    return pref*num/den


def interval(data:dict) -> tuple[fmpq,fmpq]:
    mid,rad,exp=int(data["mid"]),int(data["rad"]),int(data["exp"])
    factor=fmpq(10**exp) if exp>=0 else fmpq(1,10**(-exp))
    return fmpq(mid-rad)*factor,fmpq(mid+rad)*factor


def check_hnf(data:dict,rows:list[list[int]],cols:int) -> tuple[list[list[int]],int]:
    H=matrix([ints(row) for row in data["H"]],len(rows))
    T=matrix([ints(row) for row in data["T"]],cols)
    assert abs(int(T.det()))==1
    assert T*matrix(rows,cols).transpose()==H
    zero=[i for i in range(cols) if all(H[i,j]==0 for j in range(H.ncols()))]
    assert zero==ints(data["zero_rows"])
    basis=[ints(row) for row in data["basis"]]
    assert basis==[[int(T[i,j]) for j in range(cols)] for i in zero]
    rank=cols-len(zero)
    assert rank==int(data["rank"])
    return basis,rank


def audit_case(index:dict) -> dict:
    path=ROOT/index["artifact"]
    assert hashlib.sha256(path.read_bytes()).hexdigest()==index["artifact_sha256"]
    with gzip.open(path,"rt",encoding="utf-8") as stream:
        data=json.load(stream)
    p,n,m,R=(int(data[k]) for k in ("p","n","m","R"))
    d,b=9-p,10-p
    assert data["case_id"]==index["case_id"]
    assert d==int(data["d"]) and b==int(data["b"])
    assert 2*R<=p*(n+1)-2*b*m-2
    weighted_source=ROOT/"missions/zeta9/round5/scripts/weighted_forms.py"
    base_source=ROOT/"missions/zeta9/round2/scripts/general_poles.py"
    assert hashlib.sha256(weighted_source.read_bytes()).hexdigest()==data["source_sha256"]["weighted_forms"]
    assert hashlib.sha256(base_source.read_bytes()).hexdigest()==data["source_sha256"]["general_poles"]
    cols=R+1
    vectors=[[q(v) for v in row] for row in data["raw_monomial_vectors"]]
    orders=[int(s) for s in data["zeta_orders"]]
    assert len(vectors)==cols and orders==list(range(d+3,10,2))
    poles=[[[q(v) for v in line] for line in block]
           for block in data["monomial_pole_coefficients_r_by_j_by_s1_to_p"]]
    assert len(poles)==cols
    for r in range(cols):
        assert len(poles[r])==n+1 and all(len(line)==p for line in poles[r])
        for t in (fmpq(1,2),fmpq(m+1)):
            direct=pole_direct(p,n,m,t)*(t*(t+n))**r
            partial=sum((poles[r][j][s-1]/(t+j)**s
                         for j in range(n+1) for s in range(1,p+1)),fmpq(0))
            assert direct==partial
        rho={s:sum((poles[r][j][s-1] for j in range(n+1)),fmpq(0))
             for s in range(1,p+1)}
        assert all(rho[s]==0 for s in range(1,p+1) if s==1 or s%2==0)
        assert all(poles[r][n-j][s-1]==(-1)**(s+1)*poles[r][j][s-1]
                   for j in range(n+1) for s in range(1,p+1))
        constant=-sum((fmpq(math.comb(d+s-1,d))*poles[r][j][s-1]
                       *sum((fmpq(1,k**(d+s)) for k in range(1,j+1)),fmpq(0))
                       for j in range(n+1) for s in range(1,p+1)),fmpq(0))
        expected=[constant]+[fmpq(math.comb(order-1,d))*rho[order-d]
                             for order in orders]
        assert expected==vectors[r]
    rawrows=[[vectors[r][k] for r in range(cols)]
             for k in range(len(vectors[0]))]
    lower=rawrows[1:-1]
    for raw,den,row in zip(lower,data["lower_row_denominators"],data["lower_integer_matrix"]):
        den=int(den)
        assert den==math.lcm(*(int(x.denom()) for x in raw))
        assert ints(row)==[int((den*x).numer()) for x in raw]
    for raw,den,row in zip(rawrows,data["full_row_denominators"],data["full_integer_matrix"]):
        den=int(den)
        assert den==math.lcm(*(int(x.denom()) for x in raw))
        assert ints(row)==[int((den*x).numer()) for x in raw]
    lowrows=[ints(row) for row in data["lower_integer_matrix"]]
    fullrows=[ints(row) for row in data["full_integer_matrix"]]
    K,lowrank=check_hnf(data["low_hnf"],lowrows,cols)
    Kfull,fullrank=check_hnf(data["full_hnf"],fullrows,cols)
    image=data["image_lattice"]
    common=int(image["image_common_denominator"])
    generators=[ints(row) for row in image["image_generator_rows"]]
    assert generators==[[int((common*sum((vectors[r][key]*w[r]
                             for r in range(cols)),fmpq(0))).numer())
                          for key in (0,len(vectors[0])-1)] for w in K]
    H=matrix([ints(row) for row in image["image_H"]],2)
    U=matrix([ints(row) for row in image["image_U"]],len(K))
    assert abs(int(U.det()))==1 and U*matrix(generators,2)==H
    preimages=[ints(row) for row in image["image_preimages"]]
    assert preimages==[[sum(int(U[i,k])*K[k][j] for k in range(len(K)))
                        for j in range(cols)] for i in range(len(K))]
    nonzero=ints(image["image_nonzero_rows"])
    zero=ints(image["image_zero_rows"])
    assert nonzero==[i for i in range(len(K)) if any(H[i,j] for j in range(2))]
    assert zero==[i for i in range(len(K)) if not any(H[i,j] for j in range(2))]
    assert len(nonzero)==fullrank-lowrank==int(image["image_rank"])
    fullzero=[preimages[i] for i in zero]
    assert fullzero==[ints(row) for row in image["full_zero_from_image"]]
    assert matrix(fullzero,cols).hnf()==matrix(Kfull,cols).hnf()
    search=data["candidate_search"]
    weights=[n**(2*r) for r in range(cols)]
    assert weights==ints(search["weight_diagonal"])
    zero_lll=[ints(row) for row in search["full_zero_lll_basis"]]
    zero_T=[ints(row) for row in search["full_zero_lll_transform"]]
    if zero_T:
        assert abs(int(matrix(zero_T,len(zero_T)).det()))==1
    assert zero_lll==[[sum(zero_T[i][k]*fullzero[k][j]
                           for k in range(len(fullzero))) for j in range(cols)]
                      for i in range(len(fullzero))]
    reduced=[ints(row) for row in search["image_reduced_preimages"]]
    initial=[ints(row) for row in search["image_initial_zero_reduction"]]
    for i,pos in enumerate(nonzero):
        assert reduced[i]==[preimages[pos][j]
                            -sum(initial[i][k]*zero_lll[k][j]
                                 for k in range(len(zero_lll)))
                            for j in range(cols)]
    image_lll=[ints(row) for row in search["image_weighted_lll_basis"]]
    image_T=[ints(row) for row in search["image_weighted_lll_transform"]]
    assert abs(int(matrix(image_T,len(image_T)).det()))==1
    assert image_lll==[[sum(image_T[i][k]*reduced[k][j]
                            for k in range(len(reduced))) for j in range(cols)]
                       for i in range(len(reduced))]
    selected=search["selected"]
    assert len(selected)<=8
    assert all(int(selected[i]["weighted_W_norm_squared"])<=int(selected[i+1]["weighted_W_norm_squared"])
               for i in range(len(selected)-1))
    seen=set()
    below=0
    for candidate in selected:
        combo=ints(candidate["combo"])
        assert all(-4<=x<=4 for x in combo) and math.gcd(*combo)==1
        pre=ints(candidate["pre_sign_w"])
        removal=ints(candidate["zero_reduction_multiples"])
        assert pre==[sum(combo[i]*image_lll[i][j] for i in range(len(combo)))
                     -sum(removal[i]*zero_lll[i][j] for i in range(len(zero_lll)))
                     for j in range(cols)]
        signflip=int(candidate["sign_flip"])
        assert signflip in (-1,1)
        w=ints(candidate["w"])
        assert w==[signflip*x for x in pre]
        raw=[sum((vectors[r][k]*w[r] for r in range(cols)),fmpq(0))
             for k in range(len(rawrows))]
        assert raw==[q(x) for x in candidate["raw_vector"]]
        assert all(x==0 for x in raw[1:-1]) and raw[-1]>0
        pair=[int(x) for x in candidate["normalized"]["pair"]]
        den=math.lcm(int(raw[0].denom()),int(raw[-1].denom()))
        pres=[int((den*raw[-1]).numer()),int((den*raw[0]).numer())]
        content=math.gcd(*pres)
        multiplier=fmpq(den,content)
        assert den==int(candidate["normalized"]["denominator"])
        assert pres==ints(candidate["normalized"]["pre"])
        assert content==int(candidate["normalized"]["content"])
        assert multiplier==q(candidate["normalized"]["multiplier"])
        assert pair==[v//content for v in pres] and math.gcd(*pair)==1
        assert tuple(pair) not in seen
        seen.add(tuple(pair))
        assert sha(w)==candidate["W_sha256"]
        assert sha(pair)==candidate["primitive_pair_sha256"]
        raw_sha=hashlib.sha256(",".join(f"{x.numer()}/{x.denom()}"
                                        for x in raw).encode()).hexdigest()
        assert raw_sha==candidate["raw_vector_sha256"]
        assert sum(abs(w[j])*weights[j] for j in range(cols))==int(candidate["W_weighted_l1"])
        assert sum(abs(v) for v in w)==int(candidate["W_unweighted_l1"])
        assert sum((w[j]*weights[j])**2 for j in range(cols))==int(candidate["weighted_W_norm_squared"])
        bits=max(abs(v).bit_length() for v in pair)+400
        with ctx.workprec(bits):
            value=arb(fmpz(pair[1]))+arb(fmpz(pair[0]))*arb(9).zeta()
            sign=1 if value.lower()>0 else (-1 if value.upper()<0 else 0)
            assert sign==int(candidate["arb"]["sign"])
            assert value.rel_accuracy_bits()>=80
            abslog=(value if sign>0 else -value).log()
            assert bool(abslog.upper()<0)==candidate["arb"]["below_one"]
            assert abs(float(abslog)/n-candidate["arb"]["abs_log_per_n"])<1e-9
            saved_interval=interval(candidate["arb"]["value_interval"])
            assert saved_interval[0]<=value.upper() and saved_interval[1]>=value.lower()
            below+=bool(abslog.upper()<0)
    if data["regression"]["applicable"]:
        assert p==9 and R==3 and m==n
        old=[int(x) for x in data["regression"]["old_pair_A9_B"]]
        assert selected[0]["normalized"]["pair"]==[str(x) for x in old] or \
               selected[0]["normalized"]["pair"]==[str(-x) for x in old]
    return {"case_id":data["case_id"],"p":p,"n":n,"m":m,"R":R,
            "low_rank":lowrank,"full_rank":fullrank,
            "full_zero_rank":len(Kfull),"image_rank":len(nonzero),
            "selected":len(selected),"below_one":below,
            "rn_min_selected":min(c["arb"]["abs_log_per_n"] for c in selected),
            "first_original_norm_log_per_n":selected[0]["arb"]["abs_log_per_n"],
            "regression":bool(data["regression"]["applicable"]),
            "artifact_sha256":index["artifact_sha256"]}


def main() -> None:
    rows=[json.loads(line) for line in INDEX.read_text(encoding="utf-8").splitlines()
          if line.strip()]
    latest={row["case_id"]:row for row in rows}
    audited=[audit_case(row) for row in latest.values() if row["status"]=="ok"]
    audited.sort(key=lambda r:(r["n"],-r["p"],r["R"]))
    result={"status":"ok","cases":len(audited),
            "below_one_candidates":sum(r["below_one"] for r in audited),
            "blocks_with_below_one":sum(r["below_one"]>0 for r in audited),
            "regressions":sum(r["regression"] for r in audited),
            "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "rows":audited}
    (VERIFY/"weighted-audit.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps({k:result[k] for k in ("status","cases","below_one_candidates",
                                            "blocks_with_below_one","regressions")},
                     ensure_ascii=False),flush=True)


if __name__=="__main__":
    main()
