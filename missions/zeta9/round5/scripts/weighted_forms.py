"""Exact invariant-polynomial numerator forms for the zeta(9) fifth round.

Only integer W(t(t+n)) coefficients are searched.  HNF transformations, rather
than rational nullspace vectors, preserve their saturated integer kernel.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"tmp/zeta7/exact_packages"))
sys.path.insert(0,str(ROOT/"missions/zeta9/round2/scripts"))
from flint import fmpq,fmpz_mat  # type: ignore
from general_poles import exact_vector,harmonic_arrays,score_value  # type: ignore

VERIFY=ROOT/"missions/zeta9/round5/verification"


def qp(x:fmpq) -> list[str]:
    return [str(x.numer()),str(x.denom())]


def sha_list(values:list[int]) -> str:
    return hashlib.sha256(",".join(map(str,values)).encode()).hexdigest()


def rows_of(M:fmpz_mat) -> list[list[int]]:
    return [[int(M[i,j]) for j in range(M.ncols())] for i in range(M.nrows())]


def mat(rows:list[list[int]],columns:int) -> fmpz_mat:
    return fmpz_mat(rows) if rows else fmpz_mat(0,columns)


def hnf_integer_kernel(rows:list[list[int]],columns:int) -> dict:
    """Saturated Z-kernel via unimodular row HNF of the transpose."""
    original=mat(rows,columns)
    H,T=original.transpose().hnf(transform=True)
    if abs(int(T.det()))!=1 or T*original.transpose()!=H:
        raise AssertionError("HNF transform is not unimodular/correct")
    nonzero=[i for i in range(columns)
             if any(H[i,j]!=0 for j in range(H.ncols()))]
    zero=[i for i in range(columns) if i not in nonzero]
    basis=[[int(T[i,j]) for j in range(columns)] for i in zero]
    if any(sum(rows[k][j]*v[j] for j in range(columns))
           for v in basis for k in range(len(rows))):
        raise AssertionError("HNF kernel row does not solve exact system")
    return {"rank":len(nonzero),"basis":basis,"H":rows_of(H),
            "T":rows_of(T),"zero_rows":zero}


def exact_row_matrix(vectors:list[list[fmpq]]) -> tuple[list[list[int]],list[int]]:
    """Input is a list of rational rows; clear *rows*, never columns."""
    denominators=[math.lcm(*(int(v.denom()) for v in row)) for row in vectors]
    rows=[[int((den*value).numer()) for value in row]
          for row,den in zip(vectors,denominators)]
    return rows,denominators


def raw_fraction(t:fmpq,p:int,n:int,m:int,b:int) -> fmpq:
    pref=fmpq(math.factorial(n)**p,math.factorial(m)**(2*b))
    numerator=(math.prod((t-j for j in range(1,m+1)),start=fmpq(1))
               *math.prod((t+n+j for j in range(1,m+1)),start=fmpq(1)))**b
    return pref*numerator/math.prod(((t+j)**p for j in range(n+1)),start=fmpq(1))


def monomial_forms(p:int,n:int,m:int,R:int,check_points:bool=True) -> dict:
    base=exact_vector(p,n,m,check_points=check_points)
    safe=base["r"]
    if R<0 or 2*R>safe:
        raise ValueError(f"Each u^rR must be O(t^-2): require 2R <= {safe}")
    d,b=base["d"],base["b"]
    orders=base["zeta_orders"]
    q=len(orders)
    harmonics=harmonic_arrays(n,range(d+1,10))
    all_poles=[{s:[] for s in range(1,p+1)} for _ in range(R+1)]
    for j in range(n+1):
        u0=j*(j-n)
        u1=n-2*j
        series=[1]+[0]*(p-1)
        for r in range(R+1):
            for s in range(1,p+1):
                coefficient=sum((series[h]*base["pole_coeffs"][s+h][j]
                                 for h in range(p-s+1)),fmpq(0))
                all_poles[r][s].append(coefficient)
            if r<R:
                nxt=[0]*p
                for h in range(p):
                    nxt[h]=u0*series[h]
                    if h>=1:
                        nxt[h]+=u1*series[h-1]
                    if h>=2:
                        nxt[h]+=series[h-2]
                series=nxt
    vectors=[]
    for r,poles in enumerate(all_poles):
        rho={s:sum(poles[s],fmpq(0)) for s in range(1,p+1)}
        if any(rho[s] for s in range(1,p+1) if s==1 or s%2==0):
            raise AssertionError("Odd-reflection/decay cancellation failed")
        if any(poles[s][n-j]!=(-1)**(s+1)*poles[s][j]
               for s in range(1,p+1) for j in range(n+1)):
            raise AssertionError("Invariant multiplier broke reflection")
        coeffs=[fmpq(math.comb(order-1,d))*rho[order-d]
                for order in orders]
        constant=-sum((fmpq(math.comb(d+s-1,d))*poles[s][j]
                       *harmonics[d+s][j]
                       for s in range(1,p+1) for j in range(n+1)),fmpq(0))
        vectors.append([constant]+coeffs)
        if check_points:
            for t in (fmpq(1,2),fmpq(m+1),fmpq(n+m+2)):
                direct=raw_fraction(t,p,n,m,b)*(t*(t+n))**r
                partial=sum((poles[s][j]/(t+j)**s
                             for s in range(1,p+1) for j in range(n+1)),fmpq(0))
                if direct!=partial:
                    raise AssertionError("Multiplied rational/PF identity failed")
    return {"p":p,"n":n,"m":m,"R":R,"d":d,"b":b,
            "safe_degree_margin":safe-2*R,"orders":orders,
            "poles":all_poles,"raw_vectors":vectors,
            "base_top_residues":base["C"]}


def weighted_norm(w:list[int],weights:list[int]) -> int:
    return sum((x*scale)**2 for x,scale in zip(w,weights))


def lll_rows(rows:list[list[int]],weights:list[int]) -> tuple[list[list[int]],list[list[int]]]:
    if not rows:
        return [],[]
    weighted=[[v*weights[j] for j,v in enumerate(row)] for row in rows]
    reduced,T=mat(weighted,len(weights)).lll(transform=True,gram="exact")
    transform=rows_of(T)
    unweighted=[[sum(transform[i][k]*rows[k][j] for k in range(len(rows)))
                 for j in range(len(weights))] for i in range(len(rows))]
    if [[v*weights[j] for j,v in enumerate(row)] for row in unweighted]!=rows_of(reduced):
        raise AssertionError("Weighted LLL transform failed")
    if abs(int(T.det()))!=1:
        raise AssertionError("LLL transform not unimodular")
    return unweighted,transform


def nearest_fraction(x:Fraction) -> int:
    """Nearest integer, deterministic half ties toward +infinity."""
    return (2*x.numerator+x.denominator)//(2*x.denominator)


def reduce_mod_full_zero(w:list[int],zero_basis:list[list[int]],
                         weights:list[int]) -> tuple[list[int],list[int]]:
    if not zero_basis:
        return list(w),[]
    originals=[[Fraction(v*weights[j]) for j,v in enumerate(row)]
               for row in zero_basis]
    stars=[]
    def dot(a,b):
        return sum((x*y for x,y in zip(a,b)),Fraction(0))
    for vec in originals:
        star=list(vec)
        for prior in stars:
            factor=dot(vec,prior)/dot(prior,prior)
            star=[x-factor*y for x,y in zip(star,prior)]
        if not dot(star,star):
            raise AssertionError("Full-zero basis is dependent")
        stars.append(star)
    current=list(w)
    steps=[0]*len(zero_basis)
    for i in reversed(range(len(zero_basis))):
        weighted=[Fraction(v*weights[j]) for j,v in enumerate(current)]
        multiple=nearest_fraction(dot(weighted,stars[i])/dot(stars[i],stars[i]))
        if multiple:
            current=[x-multiple*y for x,y in zip(current,zero_basis[i])]
            steps[i]+=multiple
    # Exact local descent makes the chosen representative smaller or equal.
    for _ in range(4*len(zero_basis)+4):
        changed=False
        present=weighted_norm(current,weights)
        for i,z in enumerate(zero_basis):
            cross=sum(current[j]*z[j]*weights[j]**2 for j in range(len(weights)))
            square=weighted_norm(z,weights)
            multiple=nearest_fraction(Fraction(cross,square))
            if not multiple:
                continue
            candidate=[current[j]-multiple*z[j] for j in range(len(weights))]
            newnorm=weighted_norm(candidate,weights)
            if newnorm<present:
                current=candidate
                steps[i]+=multiple
                present=newnorm
                changed=True
        if not changed:
            break
    if [w[j]-sum(steps[i]*zero_basis[i][j] for i in range(len(zero_basis)))
        for j in range(len(weights))]!=current:
        raise AssertionError("Full-zero coset reduction identity failed")
    return current,steps


def primitive_pair(A:fmpq,B:fmpq) -> dict:
    denominator=math.lcm(int(A.denom()),int(B.denom()))
    pre=[int((A*denominator).numer()),int((B*denominator).numer())]
    content=math.gcd(*pre)
    if content==0:
        return {"status":"zero"}
    pair=[v//content for v in pre]
    multiplier=fmpq(denominator,content)
    if [multiplier*A,multiplier*B]!=[fmpq(v) for v in pair]:
        raise AssertionError("Primitive multiplier identity failed")
    return {"status":"ok","denominator":denominator,"pre":pre,
            "content":content,"pair":pair,"multiplier":multiplier}


def integer_lattice(form:dict) -> dict:
    vectors=form["raw_vectors"]
    columns=len(vectors)
    row_vectors=[[vectors[r][k] for r in range(columns)]
                 for k in range(len(vectors[0]))]
    lower_rows,lower_den=exact_row_matrix(row_vectors[1:-1])
    full_rows,full_den=exact_row_matrix(row_vectors)
    low=hnf_integer_kernel(lower_rows,columns)
    full=hnf_integer_kernel(full_rows,columns)
    K=low["basis"]
    if len(K)!=columns-low["rank"]:
        raise AssertionError("Low kernel dimension mismatch")
    for v in full["basis"]:
        if any(sum(row[j]*v[j] for j in range(columns)) for row in lower_rows):
            raise AssertionError("Full-zero direction not in low kernel")
    if not K:
        return {"low":low,"full":full,"lower_rows":lower_rows,
                "lower_den":lower_den,"full_rows":full_rows,"full_den":full_den,
                "image_status":"empty"}
    pairs=[(sum((vectors[r][0]*w[r] for r in range(columns)),fmpq(0)),
            sum((vectors[r][-1]*w[r] for r in range(columns)),fmpq(0)))
           for w in K]
    common=math.lcm(*(int(x.denom()) for pair in pairs for x in pair))
    image=[[int((common*x).numer()) for x in pair] for pair in pairs]
    H,U=mat(image,2).hnf(transform=True)
    if U*mat(image,2)!=H or abs(int(U.det()))!=1:
        raise AssertionError("Image HNF transform is not exact unimodular")
    Hrows=rows_of(H)
    Urows=rows_of(U)
    preimages=[[sum(Urows[i][k]*K[k][r] for k in range(len(K)))
                for r in range(columns)] for i in range(len(K))]
    for i,w in enumerate(preimages):
        pair=[sum((vectors[r][key]*w[r] for r in range(columns)),fmpq(0))
              for key in (0,len(vectors[0])-1)]
        if [int((common*x).numer()) for x in pair]!=Hrows[i]:
            raise AssertionError("Image HNF lost its integer preimage")
    nonzero=[i for i,row in enumerate(Hrows) if any(row)]
    zero=[i for i,row in enumerate(Hrows) if not any(row)]
    image_rank=len(nonzero)
    if image_rank!=full["rank"]-low["rank"]:
        raise AssertionError("Full/low rank difference disagrees with image rank")
    zero_rows=[preimages[i] for i in zero]
    if mat(zero_rows,columns).hnf()!=mat(full["basis"],columns).hnf():
        raise AssertionError("Image-zero lattice is not the complete full kernel")
    return {"low":low,"full":full,"lower_rows":lower_rows,
            "lower_den":lower_den,"full_rows":full_rows,"full_den":full_den,
            "image_status":"ok","image_common_denominator":common,
            "image_generator_rows":image,"image_H":Hrows,"image_U":Urows,
            "image_rank":image_rank,"image_preimages":preimages,
            "image_nonzero_rows":nonzero,"image_zero_rows":zero,
            "full_zero_from_image":zero_rows}


def search_candidates(form:dict,lattice:dict) -> dict:
    if lattice["image_status"]!="ok" or lattice["image_rank"]==0:
        return {"status":"no_nonzero_image","examined":0,"selected":[]}
    n,R=form["n"],form["R"]
    vectors=form["raw_vectors"]
    columns=R+1
    weights=[n**(2*r) for r in range(columns)]
    zero=lattice["full_zero_from_image"]
    zero_lll,zero_T=lll_rows(zero,weights)
    image_original=[lattice["image_preimages"][i]
                    for i in lattice["image_nonzero_rows"]]
    image_reduced=[]
    image_cosets=[]
    for w in image_original:
        reduced,multiples=reduce_mod_full_zero(w,zero_lll,weights)
        image_reduced.append(reduced)
        image_cosets.append(multiples)
    image_lll,image_T=lll_rows(image_reduced,weights)
    rank=len(image_lll)
    assert 1<=rank<=2
    candidates=[]
    zero_records=[]
    constant_records=[]
    for combo in itertools.product(range(-4,5),repeat=rank):
        if not any(combo) or math.gcd(*combo)!=1:
            continue
        if next(x for x in combo if x)!=abs(next(x for x in combo if x)):
            continue
        original=[sum(combo[i]*image_lll[i][r] for i in range(rank))
                  for r in range(columns)]
        w,zero_multiple=reduce_mod_full_zero(original,zero_lll,weights)
        raw=[sum((vectors[r][k]*w[r] for r in range(columns)),fmpq(0))
             for k in range(len(vectors[0]))]
        if any(raw[1:-1]):
            raise AssertionError("Generated W did not cancel lower zeta values")
        if all(v==0 for v in raw):
            zero_records.append({"combo":list(combo),"w":w,
                                 "zero_reduction_multiples":zero_multiple,
                                 "raw_vector":raw})
            continue
        if raw[-1]==0:
            constant_records.append({"combo":list(combo),"w":w,
                                     "zero_reduction_multiples":zero_multiple,
                                     "raw_vector":raw,
                                     "weighted_W_norm_squared":weighted_norm(w,weights)})
            continue
        pre_sign_w=list(w)
        sign_flip=1
        if raw[-1]<0:
            w=[-x for x in w]
            raw=[-x for x in raw]
            sign_flip=-1
        normalized=primitive_pair(raw[-1],raw[0])
        assert normalized["status"]=="ok" and normalized["pair"][0]>0
        key=tuple(normalized["pair"])
        height=max(abs(x).bit_length() for x in key)
        unweighted_l1=sum(abs(x) for x in w)
        weighted_l1=sum(abs(w[r])*weights[r] for r in range(columns))
        candidates.append({"combo":list(combo),"w":w,"pre_sign_w":pre_sign_w,
                           "sign_flip":sign_flip,
                           "zero_reduction_multiples":zero_multiple,
                           "raw_vector":raw,"normalized":normalized,
                           "W_sha256":sha_list(w),
                           "primitive_pair_sha256":sha_list(normalized["pair"]),
                           "raw_vector_sha256":hashlib.sha256(",".join(
                               f"{v.numer()}/{v.denom()}" for v in raw).encode()).hexdigest(),
                           "height_bits":height,
                           "W_unweighted_l1":unweighted_l1,
                           "W_weighted_l1":weighted_l1,
                           "W_log_unweighted_l1_per_n":math.log(unweighted_l1)/n,
                           "W_log_weighted_l1_per_n":math.log(weighted_l1)/n,
                           "weighted_W_norm_squared":weighted_norm(w,weights)})
    candidates.sort(key=lambda item:(item["weighted_W_norm_squared"],
                   item["W_unweighted_l1"],item["height_bits"],
                   item["normalized"]["pair"],item["combo"]))
    distinct=[]
    seen=set()
    for candidate in candidates:
        key=tuple(candidate["normalized"]["pair"])
        if key not in seen:
            distinct.append(candidate)
            seen.add(key)
    selected=distinct[:8]
    for row in selected:
        A,B=row["normalized"]["pair"]
        score=score_value([9],[A],B)
        score["abs_log_per_n"]=score["abs_log_value"]/n
        row["arb"]=score
    return {"status":"ok","weight_diagonal":weights,
            "ranking_order":"exact weighted W squared norm, then unweighted W L1, then primitive coefficient bits",
            "enumeration":"coprime image-basis coordinates in [-4,4], sign-canonical",
            "full_zero_lll_basis":zero_lll,"full_zero_lll_transform":zero_T,
            "image_reduced_preimages":image_reduced,
            "image_initial_zero_reduction":image_cosets,
            "image_weighted_lll_basis":image_lll,
            "image_weighted_lll_transform":image_T,
            "examined":len(candidates)+len(zero_records)+len(constant_records),
            "distinct_effective":len(distinct),
            "skipped":{"zero_full":len(zero_records),
                       "constant_only":len(constant_records),
                       "duplicate":len(candidates)-len(distinct)},
            "zero_full_records":zero_records,
            "constant_only_records":constant_records,
            "selected":selected}


def regression_p9_R3(form:dict,search:dict) -> dict:
    if not (form["p"]==9 and form["R"]==3 and form["m"]==form["n"]):
        return {"applicable":False}
    n=form["n"]
    path=(ROOT/"missions/zeta9/round2/verification/elimination-combinations"/
          f"p9-n{n}-m{n}..{n+3}.json.gz")
    with gzip.open(path,"rt",encoding="utf-8") as stream:
        old=json.load(stream)
    if old["status"]!="ok":
        raise AssertionError("Old p9 adjacent-m reference is not an exact form")
    target=[int(x) for x in old["primitive_coefficients_A9_B"]]
    current=search["selected"][0]["normalized"]["pair"]
    if current!=target and current!=[-x for x in target]:
        raise AssertionError("R3 invariant-polynomial space disagrees with old adjacent-m form")
    return {"applicable":True,"matches_old_primitive_up_to_sign":True,
            "old_artifact":str(path.relative_to(ROOT)),
            "old_artifact_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
            "old_pair_A9_B":[str(x) for x in target]}


def serializable(value):
    if isinstance(value,bool):
        return value
    if isinstance(value,fmpq):
        return qp(value)
    if isinstance(value,dict):
        return {k:serializable(v) for k,v in value.items()}
    if isinstance(value,list):
        return [serializable(v) for v in value]
    if isinstance(value,tuple):
        return [serializable(v) for v in value]
    if isinstance(value,int):
        return str(value)
    return value


def block_case_id(p:int,n:int,m:int,R:int) -> str:
    return f"p{p}-n{n}-m{m}-R{R}"


def build_block(p:int,n:int,m:int,R:int,write:bool=True) -> dict:
    start=time.monotonic()
    form=monomial_forms(p,n,m,R,check_points=True)
    lattice=integer_lattice(form)
    search=search_candidates(form,lattice)
    regression=regression_p9_R3(form,search)
    case=block_case_id(p,n,m,R)
    source=Path(__file__)
    artifact={"case_id":case,"definition":"integer-invariant-polynomial-W-u-v1",
              "p":p,"n":n,"m":m,"R":R,"d":form["d"],"b":form["b"],
              "safe_degree_margin":form["safe_degree_margin"],
              "u":"t(t+n)","W_basis_exponents":list(range(R+1)),
              "zeta_orders":form["orders"],
              "vector_order":"[constant, lower odd zeta, ..., zeta(9)]",
              "raw_monomial_vectors":form["raw_vectors"],
              "monomial_pole_coefficients_r_by_j_by_s1_to_p":
                  [[[form["poles"][r][s][j] for s in range(1,p+1)]
                    for j in range(n+1)] for r in range(R+1)],
              "base_top_residues":form["base_top_residues"],
              "lower_integer_matrix":lattice["lower_rows"],
              "lower_row_denominators":lattice["lower_den"],
              "full_integer_matrix":lattice["full_rows"],
              "full_row_denominators":lattice["full_den"],
              "low_hnf":lattice["low"],"full_hnf":lattice["full"],
              "image_lattice":{k:v for k,v in lattice.items()
                               if k.startswith("image_") or k=="full_zero_from_image"},
              "candidate_search":search,"regression":regression,
              "seconds":round(time.monotonic()-start,3),
              "source_sha256":{
                  "weighted_forms":hashlib.sha256(source.read_bytes()).hexdigest(),
                  "general_poles":hashlib.sha256((ROOT/"missions/zeta9/round2/scripts/general_poles.py").read_bytes()).hexdigest()}}
    if write:
        VERIFY.mkdir(parents=True,exist_ok=True)
        path=VERIFY/f"weighted-{case}.json.gz"
        with gzip.open(path,"wt",encoding="utf-8",compresslevel=6) as stream:
            json.dump(serializable(artifact),stream,ensure_ascii=False,
                      separators=(",",":"))
        first=search["selected"][0] if search["selected"] else None
        brief={"case_id":case,"status":search["status"],"p":p,"n":n,"m":m,"R":R,
               "low_rank":lattice["low"]["rank"],
               "full_rank":lattice["full"]["rank"],
               "full_zero_rank":len(lattice["full"]["basis"]),
               "image_rank":lattice.get("image_rank",0),
               "distinct_effective":search.get("distinct_effective",0),
               "selected_count":len(search["selected"]),
               "best_height_bits":first["height_bits"] if first else None,
               "best_W_log_unweighted_l1_per_n":first["W_log_unweighted_l1_per_n"] if first else None,
               "best_W_log_weighted_l1_per_n":first["W_log_weighted_l1_per_n"] if first else None,
               "best_log_abs_per_n":first["arb"]["abs_log_per_n"] if first else None,
               "best_below_one":first["arb"]["below_one"] if first else None,
               "any_below_one":any(row["arb"]["below_one"] for row in search["selected"]),
               "regression_match":regression.get("matches_old_primitive_up_to_sign"),
               "seconds":artifact["seconds"],
               "artifact":str(path.relative_to(ROOT)).replace("\\","/"),
               "artifact_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
               "source_sha256":artifact["source_sha256"]}
        return brief
    return artifact


def self_test() -> dict:
    example=hnf_integer_kernel([[2,1,1]],3)
    kernel=example["basis"]
    target=[-1,1,1]
    enlarged=[row for row in rows_of(mat(kernel+[target],3).hnf()) if any(row)]
    canonical=[row for row in rows_of(mat(kernel,3).hnf()) if any(row)]
    if enlarged!=canonical:
        raise AssertionError("Integer kernel is not saturated on regression matrix")
    p5=monomial_forms(5,6,1,2,check_points=True)
    assert p5["raw_vectors"][0]==exact_vector(5,6,1)["raw_vector"]
    p9=monomial_forms(9,6,1,3,check_points=True)
    assert p9["raw_vectors"][0]==exact_vector(9,6,1)["raw_vector"]
    return {"status":"ok","saturated_kernel_example":True,
            "p5_and_p9_direct_rational_PF":True,
            "base_vector_regression":True}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--p",type=int)
    parser.add_argument("--n",type=int)
    parser.add_argument("--m",type=int)
    parser.add_argument("--R",type=int)
    parser.add_argument("--self-test",action="store_true")
    args=parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(),ensure_ascii=False),flush=True)
        return
    if None in (args.p,args.n,args.m,args.R):
        parser.error("Need --p --n --m --R")
    print(json.dumps(build_block(args.p,args.n,args.m,args.R),ensure_ascii=False,
                     separators=(",",":")),flush=True)


if __name__=="__main__":
    main()
