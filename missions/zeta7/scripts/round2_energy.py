"""Exploratory multilayer/shift energy comparison. NEVER a certificate.

Normalization uses factorials (2(g+i))!, consistently with
research/round2-analytic.md. Finite primitive costs use the exact same S.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys
sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tmp/zeta7/exact_packages'))
import numpy as np
from scipy.optimize import root, minimize_scalar
from flint import arb, ctx, fmpz
from energy_experiment import primitive_log, arc_potential

gx, gw = np.polynomial.legendre.leggauss(256)
theta = (gx + 1) * math.pi / 2
theta_w = gw / 2


def field(t, layers, gamma=0):
    t = np.asarray(t, dtype=float)
    val = 2 * math.pi * np.sqrt(t) + primitive_log(1, t)
    for alpha, q in layers:
        if alpha:
            val -= 2 * q * primitive_log(alpha, t)
    if gamma:
        with np.errstate(divide='ignore'):
            val -= 2 * gamma * np.log(t)
    return val


def field_prime(t, layers, gamma=0):
    st = np.sqrt(t)
    val = math.pi + np.arctan(1 / st)
    for alpha, q in layers:
        val -= 2 * q * np.arctan(alpha / st)
    return val / st - 2 * gamma / t


def support(layers, gamma, mass, guess=None):
    if guess is None:
        opt = minimize_scalar(lambda z: float(field(math.exp(z), layers, gamma)),
                              bounds=(-22, 7), method='bounded')
        center = math.exp(opt.x)
        guess = np.log([max(center * .01, 1e-10), max(mass * mass, center)])

    def equations(v):
        with np.errstate(over='ignore', invalid='ignore', divide='ignore'):
            a, width = np.exp(v)
            t = a + width / 2 * (1 + np.cos(theta))
            vp = field_prime(t, layers, gamma)
        return [float(np.dot(theta_w, vp)), float(np.dot(theta_w, t * vp)) - 2 * mass]

    sol = root(equations, guess, tol=1e-10)
    residual = max(abs(x) for x in equations(sol.x))
    if not math.isfinite(residual) or residual > 1e-6:
        raise ArithmeticError(f'one-cut solver unresolved: {sol.message}; residual={residual}')
    a, width = np.exp(sol.x)
    if not 0 < a < a + width < float('inf'):
        raise ArithmeticError('invalid support')
    return float(a), float(a + width), sol.x, residual


def assess(layers, lam, gamma=0, count=32):
    if lam <= 0 or gamma < 0 or count < 2 or any(not 0 <= a < 1 or q < 1 for a,q in layers):
        raise ValueError('Require lam>0, gamma>=0, count>=2, 0<=alpha<1, q>=1')
    x, w = np.polynomial.legendre.leggauss(count)
    masses = (x + 1) * lam / 2
    weights = w * lam / 2
    intervals, guess = [], None
    for mass in reversed(masses):
        a, b, guess, residual = support(layers, gamma, mass, guess)
        intervals.append((a, b, residual))
    intervals.reverse()
    a = np.array([v[0] for v in intervals])
    b = np.array([v[1] for v in intervals])
    if not (np.all(np.diff(a) < 0) and np.all(np.diff(b) > 0)):
        raise ArithmeticError('intervals not nested; nested energy identity unavailable')
    cumulative = np.cumsum(weights)
    energy = float(np.dot(cumulative**2 - np.r_[0, cumulative[:-1]]**2,
                          np.log((b - a) / 4)))

    def gap(t):
        t = np.atleast_1d(t)
        return 2 * sum(c * arc_potential(t, u, v) for u, v, c in zip(a, b, weights)) - field(t, layers, gamma)

    endpoint = np.sort(np.r_[0, a, b, max(2, 2 * b[-1])])
    grid = np.unique(np.r_[endpoint, np.geomspace(max(a[-1] * 1e-3, 1e-14), endpoint[-1], 3000)])
    vals = gap(grid)
    idx = int(np.argmax(vals))
    maximum, argmax = float(vals[idx]), float(grid[idx])
    for left, right in zip(endpoint[:-1], endpoint[1:]):
        opt = minimize_scalar(lambda t: -float(gap(t)[0]), bounds=(left, right),
                              method='bounded', options={'xatol': max(1e-15, (right-left)*1e-10)})
        if -opt.fun > maximum:
            maximum, argmax = float(-opt.fun), float(opt.x)
    F = lambda v: 0 if v == 0 else 3*v*v - 2*v*v*math.log(2*v)
    cstar = -2*lam + 4*lam*sum(q*alpha*(1-math.log(alpha)) for alpha,q in layers if alpha) + F(gamma+lam)-F(gamma)
    return dict(layers=layers, lam=lam, gamma=gamma, arcs=count,
                Cstar=cstar, M_sampled=maximum, M_arg=argmax, I=energy,
                U_sampled=lam*maximum-energy+cstar,
                support_residual=max(p[2] for p in intervals),
                a=a.tolist(), b=b.tolist(), c=weights.tolist(), certified=False,
                limitation='Sampled/local maximum, no global bound; not an irrationality certificate.')


def interval(v, digits=35):
    mid, rad, exp = v.mid_rad_10exp(digits)
    return dict(mid=str(mid), rad=str(rad), exp=int(exp))


def finite_cost(row):
    K, h, g = row['K'], row['h'], row.get('g', 0)
    with ctx.workprec(256):
        logS = (h-1)*arb(4).log() + 2*h*arb(fmpz(math.factorial(K))).log()
        for layer in row['layers40']:
            N = layer['N40']*K//40
            logS -= 4*layer['q']*h*arb(fmpz(math.factorial(N))).log()
        for i in range(h):
            logS -= 2*arb(fmpz(math.factorial(2*(g+i)))).log()
        scale_num = row.get('primitive_scale_numerator', row['denominator'])
        scale_den = row.get('primitive_scale_denominator', row['numerator_content'])
        logscale = arb(fmpz(scale_num)).log() - arb(fmpz(scale_den)).log()
        saved = row['log_interval']
        logP = arb(saved['mid'], saved['rad'])*arb(10)**saved['exp']
        # P = primitive_scale * Delta; F = S * Delta.
        cost = (logscale-logS)/(K*K)
        real = logP/(K*K)-cost
        return dict(C_primitive=float(cost), C_primitive_interval=interval(cost),
                    U_finite=float(real), U_finite_interval=interval(real),
                    finite_normalization='shifted factorial S', finite_decomposition_certified=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input', default='missions/zeta7/verification/round2-results.jsonl')
    p.add_argument('--out', default='missions/zeta7/verification/round2-energy.json')
    p.add_argument('--arcs', type=int, default=32)
    p.add_argument('--top', type=int, default=4)
    args = p.parse_args()
    rows = [json.loads(s) for s in (ROOT/args.input).read_text(encoding='utf-8').splitlines() if s.strip()]
    selected = []
    for route in ('A', 'B'):
        for K in (40, 80, 160):
            candidates = [r for r in rows if r.get('route') == route and r.get('K') == K and 'log_interval' in r]
            selected += sorted(candidates, key=lambda r:r['log_value_per_K2'])[:args.top]
    output, cache = [], {}
    for row in selected:
        layers = [(a['N40']/40, a['q']) for a in row['layers40']]
        lam, gamma = row['h']/row['K'], row.get('g',0)/row['K']
        key = (tuple(layers), lam, gamma)
        if key not in cache:
            try:
                cache[key] = assess(layers, lam, gamma, args.arcs)
            except Exception as exc:
                cache[key] = dict(error=str(exc), certified=False)
        val = dict(case_id=row['case_id'], route=row['route'], K=row['K'], **cache[key], **finite_cost(row))
        output.append(val)
        print(json.dumps({k:v for k,v in val.items() if k not in ('a','b','c')}, allow_nan=False), flush=True)
    dest=ROOT/args.out
    dest.write_text(json.dumps(output, indent=2, allow_nan=False)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
