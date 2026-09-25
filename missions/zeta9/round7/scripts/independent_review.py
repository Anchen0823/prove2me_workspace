"""Independent matrix and interval review of the Round7 finite evidence."""
from __future__ import annotations
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'tmp/zeta7/exact_packages'))
sys.set_int_max_str_digits(0)
from flint import fmpq,fmpz_mat,arb,ctx

BASE=ROOT/'missions/zeta9/round7'
OUT=BASE/'verification'


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def q(pair):return fmpq(int(pair[0]),int(pair[1]))
def M(rows):return fmpz_mat([[int(x) for x in row] for row in rows])
def pq(value):return [str(value.numer()),str(value.denom())]


def read(path):
    if path.suffix=='.gz':
        with gzip.open(path,'rt',encoding='utf-8') as f:return json.load(f)
    return json.loads(path.read_text(encoding='utf-8-sig'))


def run():
    source=OUT/'modulus-scan.json'; scan=read(source);checked=[]
    assert scan['source_sha256']['modulus_scan']==sha(BASE/'scripts/modulus_scan.py')
    for case in scan['cases']:
        n=int(case['n']);D=int(case['D']);s1=int(case['s1']);N=int(case['N'])
        K=M(case['K_rows']);J=M(case['J_rows_B_A']);U=M(case['smith_U']);V=M(case['smith_V'])
        assert U*J*V==M([[s1,0],[0,s1*N]])
        assert abs(int(U.det()))==abs(int(V.det()))==1
        factors=[(int(p),int(e)) for p,e in case['N_complete_small_prime_factorization']]
        assert math.prod(p**e for p,e in factors)==N
        assert all(p>1 and all(p%k for k in range(2,math.isqrt(p)+1)) for p,e in factors)
        assert int(case['d_n'])==math.lcm(*range(1,n+1))
        modes=[]
        for mode in case['modes']:
            weights=list(map(int,mode['weights']))
            weighted=M([[int(K[i,j])*weights[j] for j in range(5)] for i in range(2)])
            KG=weighted*weighted.transpose(); delta2=int(KG.det())
            assert delta2==int(mode['deltaK_squared'])
            g2_review=None
            for row in mode['tiers']:
                g=int(row['g']); assert N%g==0 and N//g==int(row['g_divides_N_quotient'])
                basis=M([[g,0],[0,1]])*U*K
                assert basis==M(row['basis_rows_diag_g_1_UK'])
                H=M(row['gauss_unimodular_H']); assert abs(int(H.det()))==1
                red=H*basis; assert red==M(row['gauss_reduced_rows'])
                WR=M([[int(red[i,j])*weights[j] for j in range(5)] for i in range(2)])
                G=WR*WR.transpose();a,b,c=int(G[0,0]),int(G[0,1]),int(G[1,1])
                assert 0<a<=c and 2*abs(b)<=a
                assert int(G.det())==g*g*delta2
                assert a==int(row['mu1_squared'])
                squared=fmpq(4*D*D*delta2,3*s1*s1*a)
                assert squared==q(row['lambda2_upper_squared_numerator_denominator'])
                with ctx.workprec(512):
                    rate=arb(squared).log()/(2*n)
                    old=row['log_lambda2_upper_per_n']
                    unit=fmpq(10)**int(old['exp'])
                    lo=(int(old['mid'])-int(old['rad']))*unit
                    hi=(int(old['mid'])+int(old['rad']))*unit
                    assert rate.lower()>=arb(lo).lower() and rate.upper()<=arb(hi).upper()
                    for threshold,rat in [('10.43',fmpq(1043,100)),('10.564',fmpq(2641,250))]:
                        decision='below' if rate.upper()<arb(rat).lower() else 'above'
                        assert decision==old['threshold_comparisons'][threshold]
                if 'gcd_N_d_n_pow_2' in row['labels']:
                    assert g==math.gcd(N,int(case['d_n'])**2)
                    g2_review=dict(rate=float(rate),strictly_below_10_564=old['threshold_comparisons']['10.564']=='below')
            modes.append(dict(mode=mode['mode'],tiers_verified=len(mode['tiers']),g2=g2_review))
        checked.append(dict(n=n,complete_factorization_verified=True,modes=modes))

    window_path=OUT/'prime-window-scan.json'
    window_data=read(window_path);windows_checked=[]
    for case in window_data['cases']:
        n=int(case['n']);N=int(case['N']);D=int(case['D']);s1=int(case['s1'])
        K=M(case['K_rows']);U=M(case['smith_U'])
        primes=[p for p in range(2,n+1) if all(p%j for j in range(2,math.isqrt(p)+1))]
        decisions=[]
        for mode in case['modes']:
            weights=list(map(int,mode['weights']))
            for row in mode['windows']:
                c=int(row['c']);g=math.gcd(N,math.prod(p*p for p in primes if c*p>n))
                assert g==int(row['g']) and N//g==int(row['N_over_g'])
                B=M([[g,0],[0,1]])*U*K;H=M(row['gauss_unimodular_H'])
                assert abs(int(H.det()))==1 and H*B==M(row['gauss_reduced_rows'])
                R=H*B;WR=M([[int(R[i,j])*weights[j] for j in range(5)] for i in range(2)])
                G=WR*WR.transpose();a,b,cc=int(G[0,0]),int(G[0,1]),int(G[1,1])
                assert 0<a<=cc and 2*abs(b)<=a
                squared=fmpq(4*D*D*int(row['deltaK_squared']),3*s1*s1*a)
                assert int(G.det())==g*g*int(row['deltaK_squared'])
                assert squared==q(row['lambda2_upper_squared_numerator_denominator'])
                with ctx.workprec(512):
                    rate=arb(squared).log()/(2*n)
                    for threshold,rat in [('10.43',fmpq(1043,100)),('10.564',fmpq(2641,250))]:
                        outcome='below' if rate.upper()<arb(rat).lower() else 'above'
                        assert outcome==row['log_lambda2_upper_per_n']['threshold_comparisons'][threshold]
                decisions.append(dict(mode=mode['mode'],c=c,rate=float(rate)))
        windows_checked.append(dict(n=n,windows_verified=decisions))

    # Independent Arb implementation of the rational-log phase argument.
    with ctx.workprec(512):
        A=fmpq(301,100)*fmpq(101,201)**10
        upper=3*arb(3).log()-20*arb(2).log()+arb(A)
        assert upper.upper()<arb(fmpq(-2641,250)).lower()
        x=arb(fmpq(1003,1000))
        value=10*x*x.log()+(x+2)*(x+2).log()-(x-1)*(x-1).log()-10*(x+1)*(x+1).log()
        assert value.lower()>arb(fmpq(-10564155,1000000)).upper()
        exponent=dict(upper_display=upper.str(30),test_point_display=value.str(30),
                      phase_upper_below_minus_10_564=True,phase_lower_above_minus_10_564155=True)

    # Recompute the rank-one diagnostics with FLINT rationals, independently of Fraction producer.
    rank=[]
    for n,digits in [(12,50),(24,100),(48,200),(96,400)]:
        path=ROOT/f'missions/zeta9/round6/verification/analytic-triangle-exact-n{n}.json.gz'
        data=read(path)
        T=[[q(x) for x in row] for row in data['inverse_output_T_rows']]
        c=[q(row['lower']) for row in data['moments']];tail=[q(row['tail']) for row in data['moments']]
        v=[[c[i]*T[i][j] for i in range(5)] for j in range(2)]
        a=sum((x*x for x in v[0]),fmpq(0));b=sum((x*y for x,y in zip(*v)),fmpq(0));cc=sum((x*x for x in v[1]),fmpq(0))
        det=a*cc-b*b;r=b/a; target=fmpq(1,10**digits)
        assert 20*det/a<target**2
        trunc=sum((tail[i]*(abs(T[i][1])+abs(r)*abs(T[i][0])) for i in range(5)),fmpq(0))
        assert trunc<target/2
        rank.append(dict(n=n,source_sha256=sha(path),rational_slope=pq(r),
                         gram_determinant_over_QBB=pq(det/a),tail_error=pq(trunc),
                         verified_error_lt_power_of_10=-digits))
    rank_path=OUT/'rank1-independent-exact.json.gz'
    with gzip.open(rank_path,'wt',encoding='utf-8') as stream:json.dump(rank,stream,separators=(',',':'))
    frozen=[]
    for suffix in ['', 'round2','round3','round4','round5','round6']:
        base=ROOT/'missions/zeta9'/suffix;path=base/'verification/artifact-manifest.json'
        old=read(path)
        for row in old:
            f=base/row['path'];assert f.stat().st_size==row['bytes'] and sha(f)==row['sha256']
        frozen.append(dict(round=suffix or 'round1',files=len(old),manifest_sha256=sha(path)))
    result=dict(status='passed',modulus_source_sha256=sha(source),cases=checked,
                prime_window_source_sha256=sha(window_path),prime_window_cases=windows_checked,
                independent_phase_review=exponent,rank1_exact_companion_sha256=sha(rank_path),
                frozen_rounds=frozen,previous_files_checked=sum(x['files'] for x in frozen),
                script_sha256=sha(Path(__file__)))
    (OUT/'independent-review.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='passed',modulus_cases=len(checked),tiers=sum(m['tiers_verified'] for c in checked for m in c['modes']),
                         rank1_cases=len(rank),previous_files_checked=result['previous_files_checked'])),flush=True)


if __name__=='__main__':run()
