import Definitions.Def_eulerMascheroni_sondowCutoff
open EulerMascheroni.Sondow
theorem EulerMascheroni.Sondow.finite_cutoff_identity (n N : ℕ) (hn : 0 < n) (hN : 0 < N) :
    I n - remainder n N = ((2*n).choose n : ℝ) *
      ((harmonic N : ℝ)-Real.log N) + L n - (A n : ℝ) + cutoffError n N := by sorry
