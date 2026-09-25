"""Independent exact mixed-minor and prime-support certificate."""
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'tmp/zeta7/exact_packages'))
sys.set_int_max_str_digits(0)
from flint import fmpq,fmpz_mat

OUT=ROOT/'missions/zeta9/round7/verification'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    results=[]
    for n in [12,24,48,96,192]:
        path=ROOT/f'missions/zeta9/round6/verification/search-input-n{n}.json.gz'
        with gzip.open(path,'rt',encoding='utf-8') as stream:data=json.load(stream)
        d=math.lcm(*range(1,n+1));q=d**9
        raw=[[fmpq(int(x[0]),int(x[1])) for x in row] for row in data['raw_monomial_vectors']]
        scaled=[[q*x for x in row] for row in raw]
        assert all(x.denom()==1 for row in scaled for x in row)
        A=fmpz_mat([[int(x.numer()) for x in row] for row in scaled])
        def minor(rows,cols):return int(fmpz_mat([[A[i,j] for j in cols] for i in rows]).det())
        low=[minor(rows,[1,2,3]) for rows in itertools.combinations(range(5),3)]
        mixed=[minor(rows,[1,2,3,out]) for rows in itertools.combinations(range(5),4) for out in [0,4]]
        delta3=math.gcd(*low);delta4=math.gcd(*mixed);det=abs(int(A.det()))
        assert delta3>0 and delta4%delta3==0
        N=int(data['SNF_s2'])//int(data['SNF_s1'])
        assert det*delta3==N*delta4**2
        assert det%N==0
        h=n//2
        detF=fmpq(math.factorial(3*h)*math.factorial(7*h),14*h*math.factorial(h)**10)
        assert detF*q**5==det
        primechecks=[]
        for p,e in data['small_prime_part']['s2']['prime_powers']:
            p,e=int(p),int(e)
            assert p<=7*n//2
            def floorlog(m):
                value=0
                while m>=p:m//=p;value+=1
                return value
            bound=45*floorlog(n)+8*floorlog(7*n//2)
            assert e<=bound
            primechecks.append([p,e,bound])
        assert int(data['small_prime_part']['s2']['unresolved_cofactor'])==1
        smooth_bound=math.lcm(*range(1,n+1))**45*math.lcm(*range(1,7*n//2+1))**8
        assert smooth_bound%N==0
        results.append(dict(n=n,input_sha256=sha(path),q=str(q),determinant_cleared=str(det),
            low3_minors=[str(x) for x in low],mixed4_minors=[str(x) for x in mixed],
            delta3=str(delta3),delta4_star=str(delta4),N=str(N),
            smith_minor_identity=True,N_divides_cleared_determinant=True,
            N_divides_lcm_power_bound=True,prime_exponents_and_uniform_bounds=primechecks))
    (OUT/'minor-smoothness-audit.json').write_text(json.dumps(dict(status='passed',cases=results,
        uniform_identity='N=abs(det(qF))*delta3/(delta4_star)^2',
        prime_support_bound='p <= 7n/2',
        divisibility_bound='N divides d_n^45*d_(7n/2)^8',script_sha256=sha(Path(__file__))),indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='passed',cases=len(results),minors_checked=20*len(results))),flush=True)


if __name__=='__main__':main()
