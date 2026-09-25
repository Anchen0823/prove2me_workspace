"""Independent elementary sign certificates by shifting the sampling half-line."""
from __future__ import annotations
import gzip
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
OUT = Path(__file__).resolve().parents[1] / 'verification'


def main():
    sturm = json.loads((OUT/'analytic-positivity.json').read_text(encoding='utf-8'))
    rows = []
    for row in sturm['rows']:
        with gzip.open(OUT/row['archive'], 'rt', encoding='utf-8') as stream:
            block = json.load(stream)
        c = block['candidate_search']['selected'][row['selected_index']]
        w, u0 = list(map(int, c['w'])), int(row['u0'])
        shifted = [sum(w[j]*math.comb(j, i)*u0**(j-i) for j in range(i, len(w)))
                   for i in range(len(w))]
        signs = [(x>0)-(x<0) for x in shifted if x]
        changes = sum(a!=b for a, b in zip(signs, signs[1:]))
        proven = signs[0] if changes == 0 else None
        assert proven == row['raw_L_sign_if_certified']
        if proven:
            assert proven == int(c['arb']['sign'])
        else:
            # One sign change and opposite endpoint/infinity signs imply one root.
            assert changes == 1 and shifted[0] < 0 < shifted[-1]
            assert row['distinct_roots_open_ray'] == 1
        rows.append(dict(case_id=row['case_id'], selected_index=row['selected_index'],
                         W_sha256=row['W_sha256'], u0=u0,
                         shifted_integer_coefficients=list(map(str, shifted)),
                         nonzero_coefficient_sign_changes=changes,
                         elementary_half_line_sign=proven,
                         sturm_and_Arb_consistent=True))
    summary = dict(status='passed', cases=len(rows),
                   elementary_half_line_sign_certificates=sum(r['elementary_half_line_sign'] is not None for r in rows),
                   one_positive_shifted_root_cases=sum(r['elementary_half_line_sign'] is None for r in rows),
                   scope='finite archived W only', rows=rows)
    (OUT/'independent-signs.json').write_text(json.dumps(summary, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in summary.items() if k!='rows'}))


if __name__ == '__main__':
    main()
