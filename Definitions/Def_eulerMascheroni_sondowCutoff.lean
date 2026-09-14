import Definitions.Def_eulerMascheroni_sondow

noncomputable section
namespace EulerMascheroni.Sondow
open Finset

def remainder (n N : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
    ((x*(1-x)*y*(1-y))^n / ((1-x*y)*(-Real.log (x*y)))) * (x*y)^N

-- The finite-shift terms in the evaluation of I_n - R_{n,N}.
def cutoffError (n N : ℕ) : ℝ :=
  (∑ i ∈ range (n+1), (n.choose i : ℝ)^2 *
    ((harmonic (N+n+i) : ℝ) - (harmonic N : ℝ))) +
  2 * ∑ i ∈ range (n+1), ∑ j ∈ Icc (i+1) n,
    ((-1:ℝ)^(i+j)*(n.choose i : ℝ)*(n.choose j : ℝ)/(j-i:ℕ)) *
      ∑ k ∈ Icc 1 (j-i), Real.log (1+(n+i+k:ℕ)/(N:ℝ))

end EulerMascheroni.Sondow
