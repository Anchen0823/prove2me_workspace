"""Root audit: full polynomial identity and original-product sums with strict tails.

Does not use partial fractions to compute the comparison sum or its tail.
The direct tail estimate is an elementary rational product majorant.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'tmp/zeta7/exact_packages'))
sys.set_int_max_str_digits(0)
from flint import arb, ctx, fmpq, fmpq_poly
from shift_forms import rational_model

OUT = ROOT / 'missions/zeta9/round3/verification'


def interval(x):
    mid, rad, exp = x.mid_rad_10exp(55)
    return dict(mid=str(mid), rad=str(rad), exp=int(exp))


def pair(q):
    return [str(q.numer()), str(q.denom())]


def polynomial_identity(model):
    D, n, m = (model[k] for k in ('D', 'n', 'm'))
    t = fmpq_poly([0, 1])
    numerator = fmpq_poly([model['F']])
    denominator = fmpq_poly([1])
    for ell in range(-D*m, D*(n+m)+1):
        numerator *= t + fmpq(ell, D)
    for j in range(n+1):
        denominator *= (t+j)**10
    reconstructed = fmpq_poly([0])
    for s in range(1, 10):
        for j, coefficient in enumerate(model['poles'][s]):
            q, r = divmod(denominator, (t+j)**s)
            assert not r
            reconstructed += coefficient*q
    assert reconstructed == numerator
    return dict(numerator_degree=numerator.degree(),
                denominator_degree=denominator.degree(),
                full_polynomial_identity=True)


def shifted_weights(D, divisors, weights):
    values = [0]*D
    for d, w in zip(divisors, weights):
        for a in range(1, d+1):
            values[a*D//d-1] += w
    assert sum(values) == sum(d*w for d, w in zip(divisors, weights))
    for s in (3, 5, 7):
        assert sum(w*d**s for d, w in zip(divisors, weights)) == 0
    return values


def original_term(D, n, m, k, a, F):
    # x=k+a/D. The D-power below includes the full, uncancelled numerator.
    if D*k+a <= D*m:
        return fmpq(0)
    M = D*(n+2*m)+1
    delta = 10*(n+1)-M
    numerator = math.prod(D*k+a+ell for ell in range(-D*m, D*(n+m)+1))
    denominator = math.prod((D*k+a+D*j)**10 for j in range(n+1))
    return F*fmpq(D**delta*numerator, denominator)


def tail_bound(D, n, m, T, a, F):
    # For k>T, x=k+a/D. Each numerator factor is <=x+n+m,
    # each denominator factor >=x. Integrate x^(-delta) from T+a/D.
    x = fmpq(D*T+a, D)
    M = D*(n+2*m)+1
    delta = 10*(n+1)-M
    assert x > m and delta >= 3
    return F*(1+fmpq(n+m)/x)**M / ((delta-1)*x**(delta-1))


def direct_check(D, n, m, T=2048):
    started = time.monotonic()
    model = rational_model(D, n, m)
    poly = polynomial_identity(model)
    values = shifted_weights(D, model['divisors'], model['weights'])
    # This extra equality independently checks the grouping used for B.
    assert sum((v*b for v, b in zip(values, model['B_a'])), fmpq(0)) == model['raw_B']
    with ctx.workprec(640):
        finite = []
        tails = []
        total = arb(0)
        radius = fmpq(0)
        shift_checks = []
        for a, weight in enumerate(values, 1):
            current = arb(0)
            for k in range(T+1):
                current += arb(original_term(D, n, m, k, a, model['F']))
            bound = tail_bound(D, n, m, T, a, model['F'])
            finite.append(interval(current))
            tails.append(pair(bound))
            total += weight*current
            radius += abs(weight)*bound
            # Hurwitz evaluation is only a comparison, not used in the sum.
            zeta_value = arb(model['B_a'][a-1])
            for s in (3, 5, 7, 9):
                zeta_value += arb(model['rho'][s])*arb(s).zeta(arb(fmpq(a, D)))
            enclosing_shift = current + arb(bound/2) + arb(0, arb(bound/2).upper())
            assert enclosing_shift.overlaps(zeta_value), (D, n, m, a)
            shift_checks.append(True)
        enclosing = total + arb(0, arb(radius).upper())
        raw = arb(model['raw_A'])*arb(9).zeta()+arb(model['raw_B'])
        assert enclosing.overlaps(raw), (D, n, m)
        direct_sign = 1 if enclosing.lower() > 0 else (-1 if enclosing.upper() < 0 else 0)
        arb_sign = 1 if raw.lower() > 0 else (-1 if raw.upper() < 0 else 0)
        assert direct_sign == arb_sign != 0, (D, n, m, str(enclosing))
        return dict(D=D, n=n, m=m, T=T, bits=640, **poly,
                    shift_weights=values, finite_shift_intervals=finite,
                    rational_shift_tail_bounds=tails,
                    independent_hurwitz_comparisons=shift_checks,
                    finite_total_interval=interval(total),
                    total_tail_radius=pair(radius),
                    direct_total_interval=interval(enclosing),
                    raw_zeta_interval=interval(raw),
                    direct_sign=direct_sign, arb_sign=arb_sign,
                    raw_A_B=[pair(model['raw_A']), pair(model['raw_B'])],
                    seconds=time.monotonic()-started)


def main():
    cases = [(6,2,0), (6,2,1), (6,4,1), (8,2,0), (8,6,1)]
    data = []
    for case in cases:
        row = direct_check(*case)
        data.append(row)
        print(json.dumps({k:row[k] for k in ('D','n','m','direct_sign','seconds')}), flush=True)
    result = dict(status='ok', cases=len(data), records=data,
                  method='full polynomial identity; original-product sums; rational integral-test tail bounds',
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT/'independent-audit.json').write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
