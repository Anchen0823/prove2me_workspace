"""Independently audit stored exact coefficients and Arb evaluations."""
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tmp/zeta7/exact_packages'))
from flint import arb, ctx, fmpz


def horner(coefficients, x):
    result = arb(0)
    for c in reversed(coefficients):
        result = result*x + fmpz(c)
    return result


def main():
    directory = ROOT / 'missions/zeta7/verification'
    report = []
    for filename in ('exact_baseline.json.gz', 'exact_K80.json.gz', 'exact_K80_s5.json.gz'):
        with gzip.open(directory/filename, 'rt', encoding='utf-8') as stream:
            rows = json.load(stream)
        for row in rows:
            coefficients = row['primitive_coefficients_ascending']
            digest = hashlib.sha256(','.join(map(str, coefficients)).encode()).hexdigest()
            assert digest == row['coefficients_sha256']
            assert math.gcd(*coefficients) == 1
            assert len(coefficients)-1 == row['degree']
            with ctx.workprec(max(row['arb_bits'], 16000)):
                z = arb(row['s']).zeta()
                # Split even/odd coefficients, independently of the original Horner path.
                v = horner(coefficients[::2], z*z) + z*horner(coefficients[1::2], z*z)
                assert v.lower() > 0
                saved = row['log_interval']
                enclosure = arb(saved['mid'], saved['rad']) * arb(10)**saved['exp']
                assert v.log().overlaps(enclosure)
                if row['s'] == 7:
                    assert v.lower() > 1
                else:
                    assert v.upper() < 1
                report.append(dict(source=filename, s=row['s'], K=row['K'], N=row['N'],
                                   q=row['q'], h=row['h'], degree=row['degree'],
                                   coefficients_sha256=digest, primitive=True,
                                   positive=True, below_one=row['s']==5,
                                   log_value=row['log_value'],
                                   log_interval=saved,
                                   independent_evaluation_accuracy_bits=v.rel_accuracy_bits()))
    (directory/'artifact-audit.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
