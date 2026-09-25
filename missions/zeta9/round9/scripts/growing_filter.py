"""Exact input and constant audit for the growing-degree resultant lemma."""
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
ROOT = BASE.parents[2]
SOURCE = ROOT / 'missions/zeta9/round8/verification/limit-obstruction.json'


def rem_gf2(f: int, g: int) -> int:
    while f and f.bit_length() >= g.bit_length():
        f ^= g << (f.bit_length() - g.bit_length())
    return f


def main() -> None:
    src = json.loads(SOURCE.read_text(encoding='utf-8'))
    q = src['inverse_primitive_charpoly']
    f = src['forward_charpoly']
    assert q == [-1, -10336452, -10120051241400,
                 -82488337575256095, -33339376907507494, 22235661]
    assert [int(x) for x in f] == [-22235661, 33339376907507494,
                                    82488337575256095, 10120051241400,
                                    10336452, 1]
    f2 = sum((int(c) & 1) << i for i, c in enumerate(f))
    assert f2 == 0b100101
    rems = {str(g): rem_gf2(f2, g) for g in (0b10, 0b11, 0b111)}
    assert all(x == 1 for x in rems.values())
    a = q[-1]
    max_other = max(abs(x) for x in q[:-1])
    R = 1 + (max_other + a - 1) // a
    assert R == 3709731751
    assert a * (R - 1) >= max_other
    assert a * (R - 2) < max_other
    out = {
        'status': 'passed',
        'scope': 'exact polynomial and constants for frozen G only',
        'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'Q_coefficients_ascending': q,
        'leading_coefficient': a,
        'max_other_coefficient': max_other,
        'cauchy_root_bound_integer': R,
        'forward_mod2_remainders': rems,
        'resultant_bound': 'if Q does not divide P, |P(rho)| >= a^(-d) ((d+1) H R^d)^(-4)',
        'zero_exception': 'Q divides P implies P(G)=0 by Cayley-Hamilton',
    }
    dst = BASE / 'verification/growing-filter.json'
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(json.dumps(out, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(f'passed: a={a}, R={R}, GF(2) remainders={rems}')


if __name__ == '__main__':
    main()
