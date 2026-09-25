"""Exploratory logarithmic-energy upper estimates, not certified bounds.

Uses nested arcsine comparison measures. Endpoints come from the one-cut
equilibrium equations as a numerical heuristic; sampled potential maxima
are not rigorous suprema. An explicit comparison measure can later be
certified without proving that the equilibrium heuristic is correct.
"""
import argparse
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
PACKAGES = ROOT / 'tmp/zeta7/exact_packages'
if PACKAGES.exists():
    sys.path.insert(0, str(PACKAGES))
import numpy as np
from scipy.optimize import root, minimize_scalar

gx, gw = np.polynomial.legendre.leggauss(256)
theta = (gx + 1) * math.pi / 2
theta_w = gw / 2


def primitive_log(c, t):
    t = np.asarray(t, dtype=float)
    st = np.sqrt(t)
    return c * np.log(t + c * c) - 2 * c + 2 * st * np.arctan2(c, st)


def field(t, alpha, q):
    return 2 * math.pi * np.sqrt(t) + primitive_log(1, t) - 2 * q * primitive_log(alpha, t)


def field_prime(t, alpha, q):
    st = np.sqrt(t)
    return (math.pi + np.arctan(1 / st) - 2 * q * np.arctan(alpha / st)) / st


def support(alpha, q, mass, guess=None):
    # Variables are log(a), log(b-a), keeping 0<a<b.
    if guess is None:
        t0 = minimize_scalar(lambda z: field(math.exp(z), alpha, q), bounds=(-22, 4), method='bounded')
        center = math.exp(t0.x)
        guess = np.log([max(center * .01, 1e-10), max(mass * mass, center)])

    def equations(v):
        a, width = np.exp(v)
        t = a + width / 2 * (1 + np.cos(theta))
        vp = field_prime(t, alpha, q)
        return [float(np.dot(theta_w, vp)), float(np.dot(theta_w, t * vp)) - 2 * mass]

    sol = root(equations, guess, tol=1e-10)
    residual = max(abs(x) for x in equations(sol.x))
    if not sol.success and residual > 1e-6:
        raise RuntimeError(f'support failed alpha={alpha} q={q} mass={mass}: {sol.message}, {residual}')
    a, width = np.exp(sol.x)
    return float(a), float(a + width), sol.x, residual


def arc_potential(t, a, b):
    t = np.asarray(t, dtype=float)
    center = (a + b) / 2
    rad = (b - a) / 2
    distance = np.abs(t - center)
    return np.log((np.maximum(distance, rad) + np.sqrt(np.maximum(distance * distance - rad * rad, 0))) / 2)


def measure(alpha, q, lam, count=24):
    x, w = np.polynomial.legendre.leggauss(count)
    masses = (x + 1) * lam / 2
    weights = w * lam / 2
    # Follow from large mass downward, avoiding a poor small-mass initial guess.
    intervals = []
    guess = None
    for mass in reversed(masses):
        a, b, guess, residual = support(alpha, q, mass, guess)
        intervals.append((a, b, residual))
    intervals.reverse()
    a = np.array([p[0] for p in intervals]); b = np.array([p[1] for p in intervals])
    if not (np.all(np.diff(a) < 0) and np.all(np.diff(b) > 0)):
        raise RuntimeError('Intervals not nested; energy formula inapplicable')
    return a, b, weights, max(p[2] for p in intervals)


def assess(alpha, q, lam=None, count=24):
    if lam is None:
        lam = 1 - alpha
    a, b, c, residual = measure(alpha, q, lam, count)
    cumulative = np.cumsum(c)
    energy = float(np.dot(cumulative ** 2 - np.r_[0, cumulative[:-1]] ** 2, np.log((b - a) / 4)))

    def potential_gap(t):
        t = np.atleast_1d(t)
        return 2 * sum(ci * arc_potential(t, ai, bi) for ai, bi, ci in zip(a, b, c)) - field(t, alpha, q)

    # Include endpoints, a logarithmic mesh, and local bounded optimization.
    endpoint = np.sort(np.r_[0, a, b, max(2, 2 * b[-1])])
    grid = np.unique(np.r_[endpoint, np.geomspace(max(a[-1] * 1e-3, 1e-14), endpoint[-1], 2500)])
    values = potential_gap(grid)
    index = int(np.argmax(values)); maxval = float(values[index]); maxt = float(grid[index])
    for left, right in zip(endpoint[:-1], endpoint[1:]):
        opt = minimize_scalar(lambda t: -float(potential_gap(t)[0]), bounds=(left, right), method='bounded',
                              options={'xatol': max(1e-15, (right - left) * 1e-10)})
        if -opt.fun > maxval:
            maxval, maxt = float(-opt.fun), float(opt.x)
    cstar = -2 * lam + 4 * q * alpha * lam * (1 - math.log(alpha)) + 3 * lam ** 2 - 2 * lam ** 2 * math.log(2 * lam)
    result = dict(alpha=alpha, q=q, lam=lam, arcs=count, M_sampled=maxval, M_arg=maxt,
                  I=energy, Cstar=cstar, U_sampled=lam * maxval - energy + cstar,
                  support_residual=residual, a=a.tolist(), b=b.tolist(), c=c.tolist(),
                  certified=False)
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--alpha', type=float, default=3/40)
    p.add_argument('--q', type=int, default=3)
    p.add_argument('--arcs', type=int, default=24)
    p.add_argument('--out', default='missions/zeta7/verification/energy-baseline.json')
    args = p.parse_args()
    result = assess(args.alpha, args.q, count=args.arcs)
    out = ROOT / args.out; out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ['a','b','c']}, indent=2))
