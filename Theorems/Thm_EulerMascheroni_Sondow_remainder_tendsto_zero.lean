import Definitions.Def_eulerMascheroni_sondowCutoff
open EulerMascheroni.Sondow Filter
open scoped Topology
theorem EulerMascheroni.Sondow.remainder_tendsto_zero (n : ℕ) (hn : 0 < n) :
    Tendsto (remainder n) atTop (𝓝 0) := by sorry
