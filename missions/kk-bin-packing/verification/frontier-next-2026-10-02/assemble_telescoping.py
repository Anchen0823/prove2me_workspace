"""Assemble the self-contained submission from proved geometric and trace helpers."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
mission = ROOT / 'missions/kk-bin-packing'
old = (ROOT / 'Solutions/Sol_KKBinPacking_GeometricGrouping_alg2_step3_card_le.lean').read_text(encoding='utf-8')
geometry = old[old.index('namespace KKContribution'):old.index('lemma groups_pairwise')]
geometry += old[old.index('lemma fst_mem_source'):old.index('end KKContribution')]
geometry += 'end KKContribution\n\n'
helpers = (mission / 'research/telescoping-audit/TraceBounds.lean').read_text(encoding='utf-8')
helpers = helpers[helpers.index('namespace KKTelescopeAudit'):]
helpers = helpers.replace('rw [tr.inst_succ i hi, hzero, hpairs, hbp]', 'rw [tr.inst_succ i hi, hpairs, hbp]')
helpers = helpers.replace(':= lt_of_le_of_lt hthreshold hrun', ':= by linarith')
helpers = helpers.replace('(le_div_iff₀ hg0).2 hg1', '(le_div_iff₀ hg0).2 (by simpa using hg1)')
body = (mission / 'research/telescoping-body.lean').read_text(encoding='utf-8')
source = ('-- Algorithm 2 LP telescoping, reduced to its two existing analytic milestones.\n'
          'import Theorems.Thm_KKBinPacking_GeometricGrouping_alg2_size_recursion\n'
          'import Theorems.Thm_KKBinPacking_GeometricGrouping_geomGroup_bounds\n\n'
          'set_option autoImplicit false\n\n'
          'open KKBinPacking.Shared KKBinPacking.GeometricGrouping\n\n')
source += geometry + helpers + '\n' + body
(ROOT / 'Solutions/Sol_KKBinPacking_GeometricGrouping_alg2_lin_telescoping.lean').write_text(source, encoding='utf-8')
