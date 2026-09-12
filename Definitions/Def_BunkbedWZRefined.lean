import Definitions.Def_BunkbedHypergraph

/-!
# The refined pair state space and the half-reflection involution

Sections 3.3 and 3.4 of Gladkov-Pak-Zimin, *The bunkbed conjecture is false*,
PNAS 122 (2025) e2420725122.

In the Wierman-Ziff model each hyperedge `e` carries a pair of states, one for each level, so the
per-hyperedge state space is `WZ x WZ` with 25 elements. Following the source we *refine* it by
splitting each of the two pairs `(abc, a|b|c)` and `(a|b|c, abc)` into a `+` and a `-` variant,
whose weights are `P_ab|c * P_ac|b` and `P_abc * P_a|b|c - P_ab|c * P_ac|b`. These sum to the
original weight `P_abc * P_a|b|c`, so the refinement does not change any probability; it exists
only to give the half-reflection involution a domain.

The refined space has 27 elements: the 23 ordinary pairs other than the two split ones, plus the
four variants. It is modelled here as `(WZ x WZ) + Fin 4`, with `legal` cutting out the two
now-redundant copies of the split pairs on the left summand.
-/

namespace Bunkbed.Hyper

/-- The refined per-hyperedge state space. `inl (a, b)` is the ordinary pair `(a, b)`; the four
right-hand elements are `(abc, a|b|c)+`, `(abc, a|b|c)-`, `(a|b|c, abc)+`, `(a|b|c, abc)-`. -/
abbrev WZExt := (WZ × WZ) ⊕ Fin 4

namespace WZExt

/-- The two pairs that get split are represented only on the right summand, so their copies on
the left are excluded. Exactly 27 of the 29 elements are legal. -/
def legal : WZExt → Bool
  | .inl (.abc, .a_b_c) => false
  | .inl (.a_b_c, .abc) => false
  | _ => true

/-- The underlying pair of WZ states, which is what determines the graph. -/
def toPair : WZExt → WZ × WZ
  | .inl p => p
  | .inr 0 => (.abc, .a_b_c)
  | .inr 1 => (.abc, .a_b_c)
  | .inr 2 => (.a_b_c, .abc)
  | .inr 3 => (.a_b_c, .abc)

/-- The refined weight. The `+` variants carry `P_ab|c * P_ac|b`, the `-` variants the
complementary `P_abc * P_a|b|c - P_ab|c * P_ac|b`. -/
def wt (P : WZ → ℚ) : WZExt → ℚ
  | .inl (a, b) => P a * P b
  | .inr 0 => P .ab_c * P .ac_b
  | .inr 1 => P .abc * P .a_b_c - P .ab_c * P .ac_b
  | .inr 2 => P .ab_c * P .ac_b
  | .inr 3 => P .abc * P .a_b_c - P .ab_c * P .ac_b

/-- Membership in `Λ²₊`: both components lie in `Λ = {abc, ab|c, ac|b, a|b|c}` (equivalently,
neither is `a|bc`), with the two split pairs represented by their `+` variants only. -/
def inLamSq : WZExt → Bool
  | .inl (.abc, .a_b_c) => false
  | .inl (.a_b_c, .abc) => false
  | .inl (a, b) => a != .a_bc && b != .a_bc
  | .inr 0 => true
  | .inr 1 => false
  | .inr 2 => true
  | .inr 3 => false

/-- The reflection involution: swap the two levels. It fixes the sign of a refined state. -/
def rho : WZExt → WZExt
  | .inl (a, b) => .inl (b, a)
  | .inr 0 => .inr 2
  | .inr 1 => .inr 3
  | .inr 2 => .inr 0
  | .inr 3 => .inr 1

/-- The half-reflection involution on `Λ²₊`, Definition 3.6. It is the identity on `Ω₀`, the
reflection on `Ω₁`, and swaps the `+` variants with the mixed pairs on `Ξ`. Outside `Λ²₊` it is
the identity. -/
def eta : WZExt → WZExt
  | .inr 0 => .inl (.ab_c, .ac_b)
  | .inr 2 => .inl (.ac_b, .ab_c)
  | .inl (.ab_c, .ac_b) => .inr 0
  | .inl (.ac_b, .ab_c) => .inr 2
  | .inl (.abc, .ab_c) => .inl (.ab_c, .abc)
  | .inl (.ab_c, .abc) => .inl (.abc, .ab_c)
  | .inl (.a_b_c, .ac_b) => .inl (.ac_b, .a_b_c)
  | .inl (.ac_b, .a_b_c) => .inl (.a_b_c, .ac_b)
  | q => q

end WZExt

end Bunkbed.Hyper

