"""Recheck saved numerical candidates with a finer prime-range cutoff.

This is a finite exploratory search, not an interval certificate. Invalid
allocation conditions are recorded rather than silently treated as bounds.
Run from the repository root: python missions/zeta7/scripts/refine_cutoff.py
"""
import json
from pathlib import Path

from arithmetic_bounds import arithmetic

ROOT = Path(__file__).resolve().parents[3]
DIRECTORY = ROOT / 'missions/zeta7/verification'


def main():
    candidates = {}
    for filename in ('joint-grid-cutoff.json', 'joint-grid-fewer-rows.json'):
        for row in json.loads((DIRECTORY / filename).read_text()):
            if not row:
                continue
            key = (row['alpha'], row['q'], row.get('lam', 1-row['alpha']))
            # Prefer the smaller sampled estimate if repeated; none is certified.
            if key not in candidates or row['U'] < candidates[key]:
                candidates[key] = row['U']
    results, invalid = [], []
    for (alpha, q, lam), value in candidates.items():
        H = lam + q*alpha
        lower = max(1.001, q/(2*H) + .001)
        upper = min(4.0, 1/(2*alpha) - .001)
        cutoffs = sorted(set([lower, 2., 2.5, 3.] +
                             [lower + (upper-lower)*i/8 for i in range(9)]))
        best = None
        for B in cutoffs:
            if not lower <= B <= upper:
                continue
            args = dict(alpha=alpha, q=q, lam=lam, B=B, M=400, s=7)
            try:
                ar = arithmetic(**args)
            except ValueError as exc:
                invalid.append(dict(**args, reason=str(exc)))
                continue
            row = dict(**args, U=value, A=ar['arithmetic'],
                       total=value+ar['arithmetic'],
                       allocation_margin=ar['allocation_margin'],
                       affine_check=ar['affine_check'], certified=False)
            results.append(row)
            if best is None or row['total'] < best['total']:
                best = row
        if best:
            print(json.dumps(best), flush=True)
    output = dict(results=results, invalid=invalid, certified=False,
                  warning='Potential maxima are sampled. This is not a proof of impossibility.')
    (DIRECTORY/'joint-grid-refined-cutoff.json').write_text(
        json.dumps(output, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(valid=len(results), invalid=len(invalid),
                         minimum=min(results, key=lambda r:r['total']))))


if __name__ == '__main__':
    main()
