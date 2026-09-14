import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
open scoped BigOperators
theorem EulerGammaResearch.variable_order_upper_bound (n p : ℕ) (hn : 0 < n) :
    let c : ℕ → ℚ := fun k => (n.choose k : ℚ)^2 * ((n+k).choose k : ℚ)^p /
      (k.factorial : ℚ);
    -(∑ k ∈ Finset.range (n+1), c k *
      ((p : ℚ)*harmonic (n+k) + 2*harmonic (n-k) - ((p : ℚ)+3)*harmonic k))
      / (∑ k ∈ Finset.range (n+1), c k) ≤ 3*harmonic n - (p : ℚ)/2 := by sorry
