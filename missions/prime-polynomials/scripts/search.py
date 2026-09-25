"""Exact bounded search: integer coefficients, x starts at 0, positive primes.
All leading coefficients of either sign are included. Constant terms need only
range over primes <= H; all others fail immediately. No cutoff on run length.
"""
import itertools
import json
import math
from pathlib import Path
import time

LIMIT = 2_000_000
sieve = bytearray(b'\x01') * (LIMIT + 1)
sieve[:2] = b'\x00\x00'
for p in range(2, math.isqrt(LIMIT) + 1):
    if sieve[p]:
        sieve[p*p::p] = b'\x00' * ((LIMIT-p*p)//p+1)

def prime(v):
    if v < 2:
        return False
    if v <= LIMIT:
        return bool(sieve[v])
    if v % 2 == 0:
        return False
    return all(v % d for d in range(3, math.isqrt(v)+1, 2))

def value(co, x):
    v = 0
    for a in co:
        v = v*x+a
    return v

def search(degree, height, monic=False):
    start = time.perf_counter()
    best = {'allow_repeats': {'length': -1}, 'distinct_prefix': {'length': -1}}
    count = 0
    constants = [p for p in range(2, height+1) if prime(p)]
    leading = [1] if monic else [a for a in range(-height, height+1) if a]
    for a in leading:
        for middle in itertools.product(range(-height, height+1), repeat=degree-1):
            for c in constants:
                co = (a, *middle, c)
                count += 1
                x, seen, distinct_length = 0, set(), None
                while True:
                    v = value(co, x)
                    if not prime(v):
                        break
                    if v in seen and distinct_length is None:
                        distinct_length = x
                    seen.add(v)
                    x += 1
                if distinct_length is None:
                    distinct_length = x
                for label, length in [('allow_repeats', x), ('distinct_prefix', distinct_length)]:
                    old = best[label]
                    key = (max(map(abs, co)), sum(map(abs, co)), co)
                    if length > old['length'] or (length == old['length'] and key < old['_key']):
                        best[label] = {'length': length, 'coefficients_descending': co,
                                       'next_value': value(co, length), '_key': key}
    for result in best.values():
        result.pop('_key')
        co, length = result['coefficients_descending'], result['length']
        vals = [value(co, x) for x in range(length)]
        assert all(prime(v) for v in vals)
        if result is best['distinct_prefix']:
            assert len(set(vals)) == length
        result['values'] = vals
    out = {'degree': degree, 'height': height, 'monic': monic,
           'candidates_with_prime_constant': count,
           'seconds': round(time.perf_counter()-start, 3), 'best': best}
    print(json.dumps(out), flush=True)
    return out

if __name__ == '__main__':
    cases = [(2, 10, False), (2, 41, False), (2, 100, False),
             (3, 10, False), (3, 20, False), (2, 1000, True)]
    results = [search(*case) for case in cases]
    (Path(__file__).resolve().parents[1]/'verification/results.json').write_text(
        json.dumps(results, indent=2), encoding='utf-8')
