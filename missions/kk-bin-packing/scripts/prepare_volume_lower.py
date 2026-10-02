"""Prepare local artifacts for the volume inequality; no network or credentials."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = ROOT / 'missions/kk-bin-packing'
OUT = HERE / 'verification/volume-2026-10-02'
PREAMBLE = ('import Definitions.Def_KKBinPacking_GeometricGrouping_Instance\n'
            'import Definitions.Def_KKBinPacking_Shared_ConfigLP\n'
            'open KKBinPacking.Shared')
STATEMENT = ('namespace KKBinPacking.GeometricGrouping\n'
             'theorem size_le_lin (I : Multiset ℝ) (hI : IsInstance I) :\n'
             '    SIZE I ≤ LIN I := by sorry\n'
             'end KKBinPacking.GeometricGrouping\n')

def main():
    source = (HERE / 'research/size-lower/SizeLower.lean').read_text(encoding='utf-8')
    source = source.replace('#print axioms solution', '').rstrip() + '\n'
    sol = 'Solutions/Sol_KKBinPacking_GeometricGrouping_size_le_lin.lean'
    thm = 'Theorems/Thm_KKBinPacking_GeometricGrouping_size_le_lin.lean'
    (ROOT / sol).write_text(source, encoding='utf-8')
    (ROOT / thm).write_text(PREAMBLE + '\n\n' + STATEMENT, encoding='utf-8')
    payload = {
        'env': '0df444a360eaa60ab8c11dca51a86af692955474',
        'problems': [{
            'theorem_name': 'KKBinPacking.GeometricGrouping.size_le_lin',
            'theorem_title': r'Lemma 2, volume lower bound: $SIZE(I) \le LIN(I)$',
            'formal_statement': STATEMENT,
            'preamble': PREAMBLE,
            'natural_language_statement': r'''Let $I$ be a finite multiset of item sizes in $(0,1)$. Write $SIZE(I)$ for the sum of all item sizes and $LIN(I)$ for the infimum cost of a nonnegative feasible solution of the configuration linear program, whose configurations have unit capacity. Then

$$SIZE(I) \le LIN(I).$$

This is the first inequality of Lemma 2. It is useful independently of integer rounding: it bounds the volume of an instance by any fractional packing cost, including residual instances in ALGORITHM 2.

**Formalization Note** This uses the existing real-valued instance and LP definitions without changing their hypotheses. The empty instance is included; the feasible-cost set is nonempty even then.''',
            'source': 'Karmarkar and Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, FOCS 1982, p. 313, Lemma 2, first inequality and its size-weighted proof. https://pagesperso.g-scop.grenoble-inp.fr/~newmana/OptApproxFall2016/Karmarker-Karp-BinPacking.pdf',
            'tags': ['bin-packing', 'linear-programming', 'approximation-algorithms'],
        }],
    }
    (OUT / 'lower-problem.json').write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    scope_path = HERE / 'scope.json'
    scope = json.loads(scope_path.read_text(encoding='utf-8'))
    scope['build'] = list(dict.fromkeys(scope['build'] + [sol]))
    scope['sources'] = list(dict.fromkeys(scope['sources'] + [sol, thm,
        'Theorems/Thm_KKBinPacking_GeometricGrouping_opt_le_two_size_add_one.lean']))
    scope['note'] = 'Selected submission roots and their actual dependencies; reductions retain explicit platform theorem imports.'
    scope_path.write_text(json.dumps(scope, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')

if __name__ == '__main__':
    main()
