"""Exact Smith-content and primitive inverse-lift audit for round 6.

No factorisation, zeta evaluation, or external exact-algebra library is used.
All writes are confined to round6/verification/arithmetic-*.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[4]
BASE = Path(__file__).resolve().parents[1]
OUT = BASE/'verification'


def matmul(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]


def rowmul(a,b):
    return matmul([a],b)[0]


def det(a):
    return a[0][0]*a[1][1]-a[0][1]*a[1][0]


def inverse(a):
    d = det(a)
    assert d
    return [[Q(a[1][1],d),Q(-a[0][1],d)],
            [Q(-a[1][0],d),Q(a[0][0],d)]]


def egcd(a,b):
    aa,bb = abs(a),abs(b)
    x,y,u,v = 1,0,0,1
    while bb:
        q,rr = divmod(aa,bb)
        aa,bb = bb,rr
        x,u = u,x-q*u
        y,v = v,y-q*v
    return aa,x*(1 if a>=0 else -1),y*(1 if b>=0 else -1)


def smith_primitive(J):
    """Return U,V with U*(J/gcd(J))*V=diag(1,N), by integer Euclid."""
    s1 = math.gcd(*(x for row in J for x in row))
    assert s1 and det(J)
    S = [[x//s1 for x in row] for row in J]
    original = [row[:] for row in S]
    U,V = [[1,0],[0,1]],[[1,0],[0,1]]
    if not S[0][0]:
        i,j = next((i,j) for i in range(2) for j in range(2) if S[i][j])
        if i:
            H = [[0,1],[1,0]]
            S,U = matmul(H,S),matmul(H,U)
        if j:
            H = [[0,1],[1,0]]
            S,V = matmul(S,H),matmul(V,H)
    steps = 0
    while True:
        steps += 1
        if S[1][0]:
            a,c = S[0][0],S[1][0]
            if c%a==0:
                H = [[1,0],[-c//a,1]]
            else:
                g,x,y = egcd(a,c)
                H = [[x,y],[-c//g,a//g]]
            assert det(H)==1
            S,U = matmul(H,S),matmul(H,U)
        if S[0][1]:
            a,b = S[0][0],S[0][1]
            if b%a==0:
                H = [[1,-b//a],[0,1]]
            else:
                g,x,y = egcd(a,b)
                H = [[x,-b//g],[y,a//g]]
            assert det(H)==1
            S,V = matmul(S,H),matmul(V,H)
        if S[1][0] or S[0][1]:
            continue
        if S[1][1]%S[0][0]==0:
            break
        H = [[1,1],[0,1]]
        S,U = matmul(H,S),matmul(H,U)
    for i in range(2):
        if S[i][i]<0:
            S[i] = [-x for x in S[i]]
            U[i] = [-x for x in U[i]]
    N = abs(det(J))//s1**2
    assert S==[[1,0],[0,N]]
    assert abs(det(U))==abs(det(V))==1
    assert matmul(matmul(U,original),V)==S
    return {'s1':s1,'s2':s1*N,'N':N,'U':U,'V':V,'euclidean_steps':steps}


def qload(x):
    return Q(int(x[0]),int(x[1]))


def logq(q):
    return math.log(q.numerator)-math.log(q.denominator)


def lift(pair,D,J,K):
    assert math.gcd(*pair)==1
    invF = [[D*x for x in row] for row in inverse(J)]
    v = rowmul(pair,invF)
    q = math.lcm(*(x.denominator for x in v))
    integers = [int(q*x) for x in v]
    h = math.gcd(*integers)
    z = [x//h for x in integers]
    r = Q(q,h)
    W = rowmul(z,K)
    assert math.gcd(*z)==math.gcd(*W)==1
    Jrow = rowmul(z,J)
    c = math.gcd(*Jrow)
    assert [Q(x,D) for x in Jrow]==[r*x for x in pair]
    assert r*D==c and Q(D,c)==1/r
    return {'pair_B_A':pair,'kernel_coordinates':z,'W':W,'raw_scaling_r':r,
            'primitive_multiplier_M':1/r,'image_content_c':c}


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def nearest(q):
    return (2*q.numerator+q.denominator)//(2*q.denominator)


def gauss(rows):
    b = [row[:] for row in rows]
    H = [[1,0],[0,1]]
    while True:
        if dot(b[1],b[1])<dot(b[0],b[0]):
            b.reverse()
            H.reverse()
        k = nearest(Q(dot(b[0],b[1]),dot(b[0],b[0])))
        if not k:
            break
        b[1] = [y-k*x for x,y in zip(b[0],b[1])]
        H[1] = [y-k*x for x,y in zip(H[0],H[1])]
    assert abs(det(H))==1 and matmul(H,rows)==b
    assert 2*abs(dot(*b))<=dot(b[0],b[0])<=dot(b[1],b[1])
    return b,H


def canonical(pair):
    if pair[1]<0 or (pair[1]==0 and pair[0]<0):
        return [-x for x in pair]
    return pair


def rational_rank(rows):
    a = [[Q(x) for x in row] for row in rows]
    rank = 0
    for column in range(len(a[0])):
        pivot = next((i for i in range(rank,len(a)) if a[i][column]),None)
        if pivot is None:
            continue
        a[rank],a[pivot] = a[pivot],a[rank]
        divisor = a[rank][column]
        a[rank] = [x/divisor for x in a[rank]]
        for i in range(rank+1,len(a)):
            multiple = a[i][column]
            a[i] = [x-multiple*y for x,y in zip(a[i],a[rank])]
        rank += 1
        if rank==len(a):
            break
    return rank


def minimum_l1(T,n,weighted=False,enumeration_cap=100000):
    weights = [n**(2*i) if weighted else 1 for i in range(5)]
    L = math.lcm(*(x.denominator for row in T for x in row))
    B0 = [[int(L*x)*weights[i] for i,x in enumerate(row)] for row in T]
    B,H = gauss(B0)
    seeds = [(a,b) for a,b in itertools.product(range(-1,2),repeat=2)
             if rowmul([a,b],H)[1]!=0]
    initial = min(sum(abs(x) for x in rowmul(seed,B)) for seed in seeds)
    aa,bb,cc = dot(B[0],B[0]),dot(*B),dot(B[1],B[1])
    delta = aa*cc-bb**2
    assert delta>0
    rectangle = [math.isqrt(initial**2*v//delta) for v in (cc,aa)]
    total = math.prod(2*x+1 for x in rectangle)
    if total>enumeration_cap:
        raise ValueError(f'Exact rectangle too large: {rectangle}, {total} points')
    best, solutions, count, excluded = None,[],0,0
    for a,b in itertools.product(range(-rectangle[0],rectangle[0]+1),
                                 range(-rectangle[1],rectangle[1]+1)):
        pair = rowmul([a,b],H)
        if not pair[1]:
            excluded += 1
            continue
        count += 1
        norm = sum(abs(x) for x in rowmul([a,b],B))
        if best is None or norm<best:
            best,solutions = norm,[canonical(pair)]
        elif norm==best:
            solutions.append(canonical(pair))
    pairs = [list(p) for p in sorted(set(map(tuple,solutions)))]
    assert best and best<=initial and all(math.gcd(*p)==1 for p in pairs)
    g = math.gcd(*(x for row in B0 for x in row))
    second_bound_squared = Q(4*delta,3*L*L)
    improved_second_squared = second_bound_squared/(g*g)
    successive = {'lambda1_squared':Q(aa,L*L),'lambda2_squared':Q(cc,L*L),
                  'covolume_squared':Q(delta,L**4),'all_entry_content_g':g,
                  'lambda1_denominator_lower_bound':Q(1,L),
                  'lambda1_content_lower_bound':Q(g,L),
                  'lambda2_denominator_upper_bound_squared':second_bound_squared,
                  'lambda2_content_upper_bound_squared':improved_second_squared,
                  'actual_log_lambda1_per_n':logq(Q(aa,L*L))/(2*n),
                  'actual_log_lambda2_per_n':logq(Q(cc,L*L))/(2*n),
                  'log_covolume_per_n':logq(Q(delta,L**4))/(2*n),
                  'log_denominator_lambda2_bound_per_n':logq(second_bound_squared)/(2*n),
                  'log_content_lambda2_bound_per_n':logq(improved_second_squared)/(2*n),
                  'two_independent_output_pairs_B_A':H,
                  'uses_zeta_numeric_values':False}
    assert Q(cc,L*L)<=improved_second_squared<=second_bound_squared
    return {'weighted':weighted,'weights':weights,'common_denominator_L':L,
            'integer_basis_B0':B0,'gauss_basis':B,'unimodular_H':H,
            'gram_aa_bb_cc':[aa,bb,cc],'gram_determinant':delta,
            'initial_l1':initial,'rectangle':rectangle,
            'nonconstant_points_examined':count,'constant_points_excluded':excluded,
            'minimum_integer_l1':best,'minimum_normalized_l1':Q(best,L),
            'log_minimum_per_n':logq(Q(best,L))/n,'minimizer_pairs_B_A':pairs,
            'successive_minima':successive,
            'scope':'global over all nonconstant primitive directions for this fixed n'}


def saturation_index_rank2(K):
    return math.gcd(*(K[0][i]*K[1][j]-K[0][j]*K[1][i]
                      for i,j in itertools.combinations(range(5),2)))


def audit_input(path):
    data = json.load(gzip.open(path,'rt',encoding='utf-8'))
    n = int(data['n'])
    assert int(data['p'])==9 and int(data['R'])==4 and int(data['m'])==n
    vectors = [[qload(x) for x in row] for row in data['raw_monomial_vectors']]
    assert rational_rank(vectors)==5
    K = [list(map(int,row)) for row in data['integer_W_basis_K_rows']]
    assert saturation_index_rank2(K)==1
    image = matmul(K,vectors)
    assert all(not x for row in image for x in row[1:4])
    F = [[row[0],row[-1]] for row in image]
    assert F==[[qload(x) for x in row] for row in data['raw_image_F_rows_B_A']]
    D = int(data['common_denominator_Q'])
    J = [list(map(int,row)) for row in data['J_rows_B_A']]
    assert [[D*x for x in row] for row in F]==J
    assert det(J)==int(data['J_det'])
    snf = smith_primitive(J)
    assert [snf['s1'],snf['s2']]==[int(data['SNF_s1']),int(data['SNF_s2'])]
    Uinv = inverse(snf['U'])
    assert all(x.denominator==1 for row in Uinv for x in row)
    Uinv = [[int(x) for x in row] for row in Uinv]
    checks = 0
    for x,y in itertools.product(range(-4,5),repeat=2):
        if math.gcd(x,y)!=1:
            continue
        a,b = rowmul([x,y],Uinv)
        c = math.gcd(*rowmul([x,y],J))
        assert c==snf['s1']*math.gcd(a,snf['N'])
        assert math.gcd(*rowmul([x,y],K))==1
        checks += 1
    T = matmul([[D*x for x in row] for row in inverse(J)],K)
    full = matmul(T,vectors)
    assert full==[[Q(1),Q(0),Q(0),Q(0),Q(0)],[Q(0),Q(0),Q(0),Q(0),Q(1)]]
    minima = [minimum_l1(T,n,weighted) for weighted in (False,True)]
    for result in minima:
        original_weighted_K = [[x*w for x,w in zip(row,result['weights'])] for row in K]
        original_reduced, original_H = gauss(original_weighted_K)
        mu1sq = dot(original_reduced[0],original_reduced[0])
        lower_squared = Q(D,snf['s2'])**2 * mu1sq
        covol_squared = result['successive_minima']['covolume_squared']
        upper_squared = Q(4,3)*covol_squared/lower_squared
        assert lower_squared<=result['successive_minima']['lambda1_squared']
        assert result['successive_minima']['lambda2_squared']<=upper_squared
        result['smith_kernel_bound'] = {
            'original_kernel_gauss_transform':original_H,
            'original_kernel_mu1_squared':mu1sq,
            'lambda1_lower_bound_squared':lower_squared,
            'lambda2_upper_bound_squared':upper_squared,
            'log_mu1_K_per_n':math.log(mu1sq)/(2*n),
            'log_lambda1_lower_per_n':logq(lower_squared)/(2*n),
            'log_lambda2_upper_per_n':logq(upper_squared)/(2*n),
            'formula':'lambda1(T) >= (D/s2) mu1(K); lambda2(T) <= 2/sqrt(3) covol(T) s2/(D mu1(K))'}
        result['primitive_integer_lifts'] = []
        for pair in result['minimizer_pairs_B_A']:
            item = lift(pair,D,J,K)
            preimage = rowmul(pair,T)
            assert [item['primitive_multiplier_M']*x for x in item['W']]==preimage
            norm = sum(abs(x)*w for x,w in zip(preimage,result['weights']))
            assert norm==result['minimum_normalized_l1']
            item['normalized_preimage'] = preimage
            result['primitive_integer_lifts'].append(item)
    return {'n':n,'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'status':'passed','K':K,'D':D,'J':J,'smith_certificate':snf,
            'primitive_content_formula_checks':checks,'canonical_inverse_T':T,
            'global_minima':minima}, data


def audit_search(path,proof,input_data):
    data = json.load(gzip.open(path,'rt',encoding='utf-8'))
    assert int(data['n'])==proof['n'] and data['input_sha256']==proof['input_sha256']
    T,K,D,J = proof['canonical_inverse_T'],proof['K'],proof['D'],proof['J']
    assert T==[[qload(x) for x in row] for row in data['inverse_map_E_rows_qB_qA']]
    Uinv = [[int(x) for x in row] for row in inverse(proof['smith_certificate']['U'])]
    n = proof['n']
    rows = []
    for entry in data['selected']+data.get('pure_constant_directions',[]):
        pair = list(map(int,entry['primitive_pair_B_A']))
        item = lift(pair,D,J,K)
        assert item['W']==list(map(int,entry['integer_W']))
        assert item['kernel_coordinates']==list(map(int,entry['integer_K_coordinates']))
        assert item['primitive_multiplier_M']==qload(entry['primitive_multiplier_M'])
        preimage = rowmul(pair,T)
        assert preimage==[qload(x) for x in entry['inverse_preimage_qE']]
        norm = sum(abs(x)*n**(2*j) for j,x in enumerate(preimage))
        assert norm==qload(entry['qE_weighted_l1'])
        a,b = rowmul(item['kernel_coordinates'],Uinv)
        extra = math.gcd(a,proof['smith_certificate']['N'])
        assert item['image_content_c']==proof['smith_certificate']['s1']*extra
        rows.append({'pair_B_A':pair,'extra_content_over_s1':extra,
                     'N_over_extra_content':proof['smith_certificate']['N']//extra,
                     'actual_content':item['image_content_c'],'weighted_normalized_l1':norm,
                     'weighted_global_minimizer':pair in proof['global_minima'][1]['minimizer_pairs_B_A'],
                     'is_pure_constant':not pair[1],'status':'passed'})
    return {'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'candidates':rows}


def jsonable(x):
    if isinstance(x,Q):
        return [str(x.numerator),str(x.denominator)]
    if isinstance(x,dict):
        return {key:jsonable(value) for key,value in x.items()}
    if isinstance(x,(list,tuple)):
        return [jsonable(v) for v in x]
    if isinstance(x,int) and not isinstance(x,bool) and abs(x)>2**53:
        return str(x)
    return x


def self_test():
    count = 0
    for entries in itertools.product(range(-2,3),repeat=4):
        J = [list(entries[:2]),list(entries[2:])]
        if det(J):
            smith_primitive(J)
            count += 1
    return {'small_smith_matrices':count,'status':'passed'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n',nargs='*',type=int)
    args = parser.parse_args()
    requested = set(args.n) if args.n else None
    rows,seen = [],{}
    for path in sorted(OUT.glob('search-input-n*.json.gz'),key=lambda p:int(p.stem.split('-n')[-1].split('.')[0])):
        n = int(path.stem.split('-n')[-1].split('.')[0])
        if requested is not None and n not in requested:
            continue
        row,data = audit_input(path)
        for minimum in row['global_minima']:
            for pair in minimum['minimizer_pairs_B_A']:
                seen.setdefault(tuple(pair),[]).append(n)
        search = OUT/f'search-n{n}.json.gz'
        if search.exists():
            row['search_audit'] = audit_search(search,row,data)
            for item in row['search_audit']['candidates']:
                key = tuple(item['pair_B_A'])
                seen.setdefault(key,[]).append(n)
        rows.append(row)
    duplicates = [{'pair_B_A':list(key),'n_values':sorted(set(ns))}
                  for key,ns in seen.items() if len(set(ns))>1]
    report = {'status':'passed','scope':'finite exact Smith/lift/global norm certificates, not irrationality',
              'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'smith_self_test':self_test(),'cases':rows,'repeated_primitive_forms':duplicates}
    (OUT/'arithmetic-congruence-audit.json').write_text(
        json.dumps(jsonable(report),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'passed','cases':len(rows),'repeated_forms':len(duplicates),
                      'minima':[{'n':r['n'],'minimum_log_per_n':[m['log_minimum_per_n'] for m in r['global_minima']],
                                 'rectangles':[m['rectangle'] for m in r['global_minima']],
                                 'minimizer_counts':[len(m['minimizer_pairs_B_A']) for m in r['global_minima']]} for r in rows]},default=str))


if __name__=='__main__':
    main()
