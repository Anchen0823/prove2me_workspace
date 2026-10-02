import Mathlib

namespace KKBinPacking.Shared

/-- A configuration of `I` (p. 313): a nonempty multiset of piece types (sizes occurring in
`I`) that fits in one bin. A type may occur in a configuration more often than in `I`. -/
def IsConfiguration (I : Multiset ℝ) (c : Multiset ℝ) : Prop :=
  c ≠ 0 ∧ (∀ t ∈ c, t ∈ I) ∧ c.sum ≤ 1

/-- Feasibility for the fractional bin-packing linear program (I) of p. 313: `x` assigns a
nonnegative weight to finitely many configurations, and for every piece type `t` of `I` the
number `b_t` of pieces of type `t` is at most `∑_c x_c · a_{t c}`, where `a_{t c}` is the
number of pieces of type `t` in configuration `c` (`Ax ≥ b`, `x ≥ 0`). -/
def IsLPFeasible (I : Multiset ℝ) (x : Multiset ℝ →₀ ℝ) : Prop :=
  (∀ c ∈ x.support, IsConfiguration I c) ∧ (∀ c, 0 ≤ x c) ∧
    ∀ t ∈ I.toFinset, (I.count t : ℝ) ≤ ∑ c ∈ x.support, x c * (c.count t : ℝ)

/-- The objective `1·x` of the linear program (I). -/
def lpCost (x : Multiset ℝ →₀ ℝ) : ℝ := ∑ c ∈ x.support, x c

/-- `LIN(I)`, the optimal value of the fractional bin-packing problem (p. 313). For an instance
the set is nonempty (one copy of the singleton configuration `{t}` per piece of type `t` is
feasible, since every size is `< 1`) and bounded below by `0`, so this infimum is the LP's
optimal value and never the junk value `sInf ∅`. -/
noncomputable def LIN (I : Multiset ℝ) : ℝ :=
  sInf {z : ℝ | ∃ x : Multiset ℝ →₀ ℝ, IsLPFeasible I x ∧ lpCost x = z}

/-- A basic (extreme point) feasible solution of (I) (p. 313): a feasible `x` that is not the
midpoint of two distinct feasible solutions, i.e. `x + y` and `x - y` feasible force `y = 0`. -/
def IsBasicFeasible (I : Multiset ℝ) (x : Multiset ℝ →₀ ℝ) : Prop :=
  IsLPFeasible I x ∧
    ∀ y : Multiset ℝ →₀ ℝ, IsLPFeasible I (x + y) → IsLPFeasible I (x - y) → y = 0

end KKBinPacking.Shared
