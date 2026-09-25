"""Independent original-product audit of the bounded tail-shift branch."""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import time

from independent_audit import interval, pair, shifted_weights
from tail_shift import model, ROOT, VERIFY
from flint import arb, ctx, fmpq, fmpq_poly


def audit(D, n, T=2048):
    start = time.monotonic()
    M = model(D, n)
    m = n
    t = fmpq_poly([0, 1])
    numerator = fmpq_poly([M['F']])
    denominator = fmpq_poly([1])
    shifts = list(range(-m, 0)) + list(range(n+1, n+m+1))
    for ell in shifts:
        numerator *= t+ell
    for j in range(n+1):
        denominator *= (t+j)**9
    reconstructed = fmpq_poly([0])
    for s in range(1, 10):
        for j, c in enumerate(M['poles'][s]):
            q, r = divmod(denominator, (t+j)**s)
            assert not r
            reconstructed += c*q
    assert numerator == reconstructed
    values = shifted_weights(D, M['divisors'], M['weights'])
    assert sum((v*b for v, b in zip(values, M['B_a'])), fmpq(0)) == M['raw_B']
    delta = 9*(n+1)-2*m
    with ctx.workprec(1024):
        total = arb(0)
        radius = fmpq(0)
        shift_rows = []
        for a, weight in enumerate(values, 1):
            finite = arb(0)
            for k in range(m, T+1):
                arg = D*k+a
                top = math.prod(arg+D*ell for ell in shifts)
                bottom = math.prod((arg+D*j)**9 for j in range(n+1))
                term = M['F']*fmpq(D**delta*top, bottom)
                assert term > 0
                finite += arb(term)
            x = fmpq(D*T+a, D)
            bound = M['F']*(1+fmpq(n+m)/x)**(2*m)/((delta-1)*x**(delta-1))
            enclosing_shift = finite+arb(bound/2)+arb(0, arb(bound/2).upper())
            hurwitz = arb(M['B_a'][a-1])
            for s in (3, 5, 7, 9):
                hurwitz += arb(M['rho'][s])*arb(s).zeta(arb(fmpq(a, D)))
            assert enclosing_shift.overlaps(hurwitz)
            total += weight*finite
            radius += abs(weight)*bound
            shift_rows.append(dict(a=a, finite=interval(finite), tail_bound=pair(bound),
                                   hurwitz_comparison=True))
        enclosing = total+arb(0, arb(radius).upper())
        raw = arb(M['raw_A'])*arb(9).zeta()+arb(M['raw_B'])
        assert enclosing.overlaps(raw)
        sign = 1 if enclosing.lower() > 0 else (-1 if enclosing.upper() < 0 else 0)
        assert sign != 0
        assert (raw.lower() > 0) if sign == 1 else (raw.upper() < 0)
        return dict(D=D, n=n, m=m, T=T, bits=1024, full_polynomial_identity=True,
                    shifts=shift_rows, folded_weights=values,
                    direct_interval=interval(enclosing), raw_interval=interval(raw),
                    total_tail_radius=pair(radius), sign=sign,
                    seconds=time.monotonic()-start)


def main():
    records = []
    for D, n in ((6, 6), (8, 6), (6, 12)):
        row = audit(D, n)
        records.append(row)
        print(json.dumps({k:row[k] for k in ('D','n','sign','seconds')}), flush=True)
    data = dict(status='ok', cases=len(records), records=records,
                method='full cleared-polynomial identity; original-product sums and rational integral tail majorants',
                script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (VERIFY/'tail-independent-audit.json').write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
