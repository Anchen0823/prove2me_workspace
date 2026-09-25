"""Independent exact moment/ellipse checks and final evidence collation.

This does not call the analytic producer's moment or minimization routines.
Factorial products and a bounded rectangle replace its recurrence and slices.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'tmp/zeta7/exact_packages'))
sys.set_int_max_str_digits(0)
from flint import fmpq, fmpz_mat, arb, ctx

OUT = ROOT / 'missions/zeta9/round6/verification'


def read(path):
    if path.suffix == '.gz':
        with gzip.open(path, 'rt', encoding='utf-8') as stream:
            return json.load(stream)
    return json.loads(path.read_text(encoding='utf-8-sig'))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def q(x):
    return fmpq(int(x[0]), int(x[1]))


def pair(x):
    return [str(x.numer()), str(x.denom())]


def interval_endpoints(v):
    unit = fmpq(10)**int(v['exp'])
    return (int(v['mid'])-int(v['rad']))*unit, (int(v['mid'])+int(v['rad']))*unit


def write(path, obj):
    path.write_text(json.dumps(obj, indent=2)+'\n', encoding='utf-8')


def check_triangle(n):
    started = time.monotonic()
    src = OUT / f'analytic-triangle-exact-n{n}.json.gz'
    d = read(src)
    assert d['archive_sha256'] == sha(OUT / f'search-input-n{n}.json.gz')
    search = read(OUT / f'search-n{n}.json.gz')
    E = [[q(x) for x in row] for row in search['inverse_map_E_rows_qB_qA']]
    T = [[q(x) for x in row] for row in d['inverse_output_T_rows']]
    assert T == [list(row) for row in zip(*E)]
    cutoff = d['cutoff']
    fac = [1]
    for k in range(1, cutoff+2*n+1):
        fac.append(fac[-1]*k)
    sums = [fmpq(0) for _ in range(5)]
    for k in range(n+1, cutoff+1):
        assert time.monotonic()-started < 120, 'moment review exceeded budget'
        value = fmpq(fac[n]**7 * fac[k-1]**10 * fac[k+2*n],
                     fac[k-n-1] * fac[k+n]**10)
        u = k*(k+n)
        for r in range(5):
            sums[r] += value*u**r
    lo, hi = [], []
    for r, row in enumerate(d['moments']):
        assert q(row['lower']) == sums[r]
        power = 7*n+8-2*r
        tail = fmpq(2**r*fac[n]**7*(cutoff+2*n)**(2*n),
                    power*cutoff**(power+2*n))
        assert q(row['tail']) == tail
        assert q(row['upper']) == sums[r]+tail
        lo.append(sums[r]); hi.append(sums[r]+tail)

    def poly(z):
        return [row[0]*z[0]+row[1]*z[1] for row in T]

    def norm(z, weights):
        return sum((abs(x)*w for x,w in zip(poly(z), weights)), fmpq(0))

    reviews = []
    for gr in d['gram_and_gauss']:
        weights = lo if gr['weights'] == 'lower' else hi
        G = [sum((weights[r]**2*T[r][i]*T[r][j] for r in range(5)), fmpq(0))
             for i,j in [(0,0),(0,1),(1,1)]]
        assert G == [q(x) for x in gr['gram_Q_entries_Q00_Q01_Q11']]
        assert q(gr['gram_det_covolume_squared']) == G[0]*G[2]-G[1]**2
        g1, g2 = tuple(gr['gauss_g1']), tuple(gr['gauss_g2'])
        assert abs(g1[0]*g2[1]-g1[1]*g2[0]) == 1

        def inner(v,w):
            return G[0]*v[0]*w[0]+G[1]*(v[0]*w[1]+v[1]*w[0])+G[2]*v[1]*w[1]

        a,b,c = inner(g1,g1), inner(g1,g2), inner(g2,g2)
        assert 0 < a <= c and 2*abs(b) <= a
        assert norm(g1,weights) == q(gr['gauss_triangle_norm_g1'])
        assert norm(g2,weights) == q(gr['gauss_triangle_norm_g2'])
        det = a*c-b*b
        for saved in [row for row in d['minima'] if row['weights'] == gr['weights']]:
            v = tuple(saved['output_B_A9'])
            H = norm(v,weights)
            assert H == q(saved['minimum']) and H > 0
            if saved['exclude_pure_constant']:
                assert v[1] != 0
            bounds = []
            for diagonal in (c,a):
                squared = H*H*diagonal/det
                bounds.append(math.isqrt(int(squared.numer())//int(squared.denom())))
            best = None
            for x,y in itertools.product(range(-bounds[0],bounds[0]+1), range(-bounds[1],bounds[1]+1)):
                assert time.monotonic()-started < 120, 'ellipse review exceeded budget'
                z = (x*g1[0]+y*g2[0], x*g1[1]+y*g2[1])
                if z == (0,0) or (saved['exclude_pure_constant'] and z[1] == 0):
                    continue
                h = norm(z,weights)
                if best is None or h < best:
                    best = h
            assert best == H
            reviews.append(dict(weights=gr['weights'],exclude_pure_constant=saved['exclude_pure_constant'],
                                rectangle=bounds, minimum_sha256=hashlib.sha256(str(H).encode()).hexdigest()))

    signed = next(row for row in read(OUT/'analytic-signed-exact.json.gz') if row['n'] == n)
    signs = []
    for row in signed['rows']:
        z = tuple(row['output_B_A9'])
        polynomial = poly(z)
        assert polynomial == [q(x) for x in row['W_rational']]
        center = sum((x*w for x,w in zip(polynomial,lo)), fmpq(0))
        radius = sum((abs(x)*(h-l) for x,l,h in zip(polynomial,lo,hi)), fmpq(0))
        assert center == q(row['center']) and radius == q(row['radius'])
        assert center-radius == q(row['lower']) and center+radius == q(row['upper'])
        assert abs(center)>radius and abs(center)+radius < 1
        assert norm(z,hi) < 1
        signs.append(1 if center>0 else -1)
    z1,z2 = [row['output_B_A9'] for row in signed['rows']]
    assert abs(z1[0]*z2[1]-z1[1]*z2[0]) == 1
    result=dict(status='passed',n=n,source_sha256=sha(src),factorial_product_moments=5,
                independent_rectangle_minima=reviews,independent_short_forms=2,
                signed_original_sum_signs=signs,no_zeta_numerical_input=True,
                seconds=time.monotonic()-started,script_sha256=sha(Path(__file__)))
    write(OUT/f'final-triangle-review-n{n}.json', result)
    print(json.dumps(dict(n=n,status='passed',seconds=result['seconds'],rectangles=[x['rectangle'] for x in reviews])),flush=True)


def collect():
    arithmetic = read(OUT/'arithmetic-congruence-audit.json')
    arithmetic_review = []
    for case in arithmetic['cases']:
        n = case['n']
        assert case['input_sha256'] == sha(OUT/f'search-input-n{n}.json.gz')
        K = fmpz_mat([[int(x) for x in row] for row in case['K']])
        J = fmpz_mat([[int(x) for x in row] for row in case['J']])
        smith = case['smith_certificate']
        U,V = [fmpz_mat([[int(x) for x in row] for row in smith[key]]) for key in ['U','V']]
        s1,s2 = int(smith['s1']),int(smith['s2'])
        assert abs(int(U.det())) == abs(int(V.det())) == 1
        assert U*J*V == fmpz_mat([[s1,0],[0,s2]])
        checks = []
        for entry in case['global_minima']:
            B0 = fmpz_mat([[int(x) for x in row] for row in entry['integer_basis_B0']])
            H = fmpz_mat([[int(x) for x in row] for row in entry['unimodular_H']])
            B = fmpz_mat([[int(x) for x in row] for row in entry['gauss_basis']])
            assert abs(int(H.det())) == 1 and H*B0 == B
            gram = B*B.transpose()
            a,b,c = int(gram[0,0]),int(gram[0,1]),int(gram[1,1])
            assert a>0 and a<=c and 2*abs(b)<=a
            L = int(entry['common_denominator_L'])
            delta2 = fmpq(a*c-b*b,L**4)
            assert q(entry['successive_minima']['covolume_squared']) == delta2
            bound = entry['smith_kernel_bound']
            HK = fmpz_mat([[int(x) for x in row] for row in bound['original_kernel_gauss_transform']])
            assert abs(int(HK.det()))==1
            weights = [int(x) for x in entry['weights']]
            KW = fmpz_mat([[int(K[i,j])*weights[j] for j in range(5)] for i in range(2)])
            KG = HK*KW
            GG = KG*KG.transpose()
            ka,kb,kc = int(GG[0,0]),int(GG[0,1]),int(GG[1,1])
            assert 0<ka<=kc and 2*abs(kb)<=ka
            assert ka == int(bound['original_kernel_mu1_squared'])
            lambda1_lower_sq = fmpq(int(case['D']),s2)**2*ka
            lambda2_upper_sq = fmpq(4,3)*delta2/lambda1_lower_sq
            assert lambda1_lower_sq == q(bound['lambda1_lower_bound_squared'])
            assert lambda2_upper_sq == q(bound['lambda2_upper_bound_squared'])
            assert fmpq(c,L**2) <= lambda2_upper_sq
            checks.append(dict(weighted=entry['weighted'],smith_bound_verified=True))
        arithmetic_review.append(dict(n=n,smith_unimodular_identity=True,checks=checks))
    frozen = []
    for suffix in ['', 'round2','round3','round4','round5']:
        base = ROOT/'missions/zeta9'/suffix
        manifest = base/'verification/artifact-manifest.json'
        rows = read(manifest)
        for row in rows:
            path = base/row['path']
            assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], str(path)
        frozen.append(dict(round=suffix or 'round1',files=len(rows),manifest_sha256=sha(manifest)))
    results=[]
    for n in [12,24,48,96,192]:
        d=read(OUT/f'independent-n{n}.json')
        search=read(OUT/f'search-n{n}.json.gz')
        assert d['input_sha256']==sha(OUT/f'search-input-n{n}.json.gz')
        assert d['search_sha256']==sha(OUT/f'search-n{n}.json.gz')
        ix=d['direct_best_selected_index']
        c=search['selected'][ix]
        M=q(c['primitive_multiplier_M'])
        lower,upper=interval_endpoints(d['direct']['original_product_sum_interval'])
        lower*=M;upper*=M
        assert lower>0 or upper<0
        bound=max(abs(lower),abs(upper))
        e=0
        while bound < fmpq(1,10**(e+1)):
            e+=1
        with ctx.workprec(256):
            display=(arb(bound).log()/arb(10).log()).str(25)
        results.append(dict(n=n,best_selected_index=ix,direct_original_product_nonzero=True,
                    primitive_direct_interval=[pair(lower),pair(upper)],
                    primitive_direct_absolute_upper=pair(bound),log10_upper_interval=display,
                    rational_denominator_strictly_greater_than_power_of_10=e,
                    certified_candidates=d['candidate_count'],
                    fixed_sign_polynomials=sum(row['sturm']['raw_L_sign_if_certified'] is not None for row in d['candidates']),
                    best_log_abs_per_n=c['log_abs_per_n']))
    write(OUT/'final-evidence.json',dict(status='passed',cases=results,
                independent_arithmetic_review=arithmetic_review,
                arithmetic_archive_sha256=sha(OUT/'arithmetic-congruence-audit.json'),
                previous_manifests_unchanged=frozen,previous_files_checked=sum(r['files'] for r in frozen),
                total_certified_candidates=sum(r['certified_candidates'] for r in results),
                finite_denominator_argument='If zeta(9)=a/b, b>0, then nonzero integer A*a+B*b has magnitude at least 1; hence b >= 1/|A*zeta(9)+B|. No irrationality follows from a finite bound.',
                triangle_n192_status='unresolved_after_120_second_cooperative_timeout_not_retried',
                script_sha256=sha(Path(__file__))))
    print(json.dumps(dict(status='passed',prior_files=sum(r['files'] for r in frozen),denominator_powers=[(r['n'],r['rational_denominator_strictly_greater_than_power_of_10']) for r in results])),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--n',type=int)
    parser.add_argument('--collect',action='store_true')
    args=parser.parse_args()
    if args.n: check_triangle(args.n)
    if args.collect: collect()
