"""Prepare the source-faithful Lemma 2 reduction and two core statements offline."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = ROOT / 'missions/kk-bin-packing'
OUT = HERE / 'verification/volume-2026-10-02'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
BASE = ('import Definitions.Def_KKBinPacking_GeometricGrouping_Instance\n'
        'import Definitions.Def_KKBinPacking_Shared_ConfigLP\n'
        'open KKBinPacking.Shared')
SOURCE = ('Karmarkar and Karp, An Efficient Approximation Scheme for the '
          'One-Dimensional Bin-Packing Problem, FOCS 1982, p. 313, Lemma 2, '
          'proof of the additive upper bound. '
          'https://pagesperso.g-scop.grenoble-inp.fr/~newmana/OptApproxFall2016/Karmarker-Karp-BinPacking.pdf')

def statement(name, body):
    return 'namespace KKBinPacking.GeometricGrouping\ntheorem ' + name + body + ' := by sorry\nend KKBinPacking.GeometricGrouping\n'

def main():
    sparse = {
        'theorem_name': 'KKBinPacking.GeometricGrouping.exists_sparse_near_optimal_lp',
        'theorem_title': r'Sparse near-optimal configuration LP solutions',
        'preamble': BASE,
        'formal_statement': statement('exists_sparse_near_optimal_lp', '''
    (I : Multiset ℝ) (hI : IsInstance I) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Multiset ℝ →₀ ℝ,
      IsLPFeasible I x ∧ lpCost x < LIN I + ε ∧
      x.support.card ≤ numSizes I'''),
        'natural_language_statement': r'''Let $I$ be a finite bin-packing instance with real item sizes in $(0,1)$, let $m(I)$ be its number of distinct sizes, and let $LIN(I)$ be the infimum of the configuration-LP objective. For every $\varepsilon>0$, there is a nonnegative feasible configuration vector $x$ such that

$$\sum_c x_c < LIN(I)+\varepsilon,
\qquad |\operatorname{supp}(x)|\le m(I).$$

This isolates the finite-dimensional LP sparsity ingredient of the additive rounding bound. It is the consequence of the optimal basic feasible solution used in the source, expressed at arbitrary positive tolerance so that later deductions do not assume infimum attainment separately. Near-optimality and the support bound are both required, including for the empty instance.''',
    }
    rounding = {
        'theorem_name': 'KKBinPacking.GeometricGrouping.lp_floor_rounding_certificate',
        'theorem_title': r'Floor-rounding certificate for a feasible configuration LP',
        'preamble': 'import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2\nopen KKBinPacking.Shared',
        'formal_statement': statement('lp_floor_rounding_certificate', '''
    (I : Multiset ℝ) (hI : IsInstance I)
    (x : Multiset ℝ →₀ ℝ) (hx : IsLPFeasible I x) :
    let R := I - (principalConfigs x).join
    ∃ P : Multiset (Multiset ℝ),
      IsPacking (I - R) P ∧
      P.card ≤ principalCount x ∧
      SIZE R ≤ lpCost x - (principalCount x : ℝ) ∧
      (OPT R : ℝ) ≤ (x.support.card : ℝ)'''),
        'natural_language_statement': r'''Let $I$ be a finite bin-packing instance with real item sizes in $(0,1)$, and let $x$ be any nonnegative feasible vector of the configuration LP. For each configuration $c$, take $\lfloor x_c\rfloor$ copies as principal bins. Write

$$N=\sum_c\lfloor x_c\rfloor,\qquad s=|\operatorname{supp}(x)|.$$

Let $R$ contain the items left after filling all available principal slots by type, with no original item used more than once. Thus its multiplicity at each size $t$ is

$$b_t(R)=\max\!\left\{b_t(I)-\sum_c\lfloor x_c\rfloor a_{tc},\,0\right\},$$

where $a_{tc}$ is the multiplicity of size $t$ in configuration $c$. There is a packing $P$ of the removed items satisfying

$$|P|\le N,\qquad SIZE(R)\le\sum_c x_c-N,\qquad OPT(R)\le s.$$

This certificate separates the combinatorial floor-and-delete operation from sparsity and LP optimality. Together with the elementary packing bound on $R$, it supplies the rounding ingredient of Lemma 2.

**Formalization Note** Multiset subtraction truncates negative counts to zero. Principal configurations may over-cover the input; $P$ contains the retained original items, with excess configuration slots removed. Empty bins are allowed. The certificate covers every feasible $x$, not only basic or optimal solutions.''',
    }
    paths = []
    for problem in [sparse, rounding]:
        problem['source'] = SOURCE
        problem['tags'] = ['bin-packing', 'linear-programming', 'approximation-algorithms']
        path = 'Theorems/Thm_' + problem['theorem_name'].replace('.', '_') + '.lean'
        (ROOT / path).write_text(problem['preamble'] + '\n\n' + problem['formal_statement'], encoding='utf-8')
        paths.append(path)
    (OUT / 'core-problems.json').write_text(json.dumps({'env': ENV, 'problems': [sparse, rounding]}, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')

    src = (HERE / 'research/rounding-upper/UpperReduction.lean').read_text(encoding='utf-8')
    src = src.replace('#print axioms KKRoundingUpper.upper_from_sparse_approx_and_rounding', '').rstrip()
    # Both residual bounds can simply be averaged, without a case split.
    if '  by_cases hsmall :' in src:
        start = src.index('  by_cases hsmall :')
        end = src.index('\n\n/-- Sparse approximate', start)
        src = src[:start] + '  linarith\n' + src[end:]
    imports = ['size_le_lin', 'lin_le_opt', 'opt_le_two_size_add_one',
               'exists_sparse_near_optimal_lp', 'lp_floor_rounding_certificate']
    src = '\n'.join('import Theorems.Thm_KKBinPacking_GeometricGrouping_' + name for name in imports) + '\n' + src
    src += '''

theorem solution (I : Multiset ℝ) (hI : IsInstance I) :
    SIZE I ≤ LIN I ∧ LIN I ≤ (OPT I : ℝ) ∧
      (OPT I : ℝ) ≤ LIN I + ((numSizes I : ℝ) + 1) / 2 := by
  refine ⟨size_le_lin I hI, lin_le_opt I hI, ?_⟩
  apply KKRoundingUpper.upper_from_sparse_approx_and_rounding
    opt_le_two_size_add_one exists_sparse_near_optimal_lp
    (fun J hJ x hx => ?_) I hI
  simpa only [KKRoundingUpper.RoundingCertificate, KKRoundingUpper.residual] using
    lp_floor_rounding_certificate J hJ x hx
'''
    sol = 'Solutions/Sol_KKBinPacking_GeometricGrouping_size_le_lin_le_opt_le_lin_add.lean'
    (ROOT / sol).write_text(src, encoding='utf-8')
    paths.append(sol)
    scope_path = HERE / 'scope.json'
    scope = json.loads(scope_path.read_text(encoding='utf-8'))
    scope['build'] = list(dict.fromkeys(scope['build'] + [sol]))
    scope['sources'] = list(dict.fromkeys(scope['sources'] + paths))
    scope_path.write_text(json.dumps(scope, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')

if __name__ == '__main__':
    main()
