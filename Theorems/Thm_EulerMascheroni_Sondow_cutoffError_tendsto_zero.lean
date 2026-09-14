import Definitions.Def_eulerMascheroni_sondowCutoff
open EulerMascheroni.Sondow Filter
open scoped Topology
theorem EulerMascheroni.Sondow.cutoffError_tendsto_zero (n : ℕ) :
    Tendsto (cutoffError n) atTop (𝓝 0) := by sorry
