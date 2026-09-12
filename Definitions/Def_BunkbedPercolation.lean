import Mathlib

/-!
# Bernoulli bond percolation and the bunkbed conjecture

Mathlib has no percolation theory of any kind, so this file supplies the objects needed to
state the bunkbed conjecture and its refutation, following

N. Gladkov, I. Pak, A. Zimin, *The bunkbed conjecture is false*,
Proc. Natl. Acad. Sci. USA **122** (2025), no. 24, e2420725122.

Everything is finite and rational-valued, hence **computable**: connection probabilities
evaluate by `#eval` and small instances close by `decide`.
-/

namespace Bunkbed

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacency of a graph presented by an explicit edge `Finset` is decidable. -/
instance fromFinsetAdj (S : Finset (Sym2 V)) :
    DecidableRel (fromEdgeSet (S : Set (Sym2 V))).Adj := fun _ _ =>
  decidable_of_iff _ (fromEdgeSet_adj (s := (S : Set (Sym2 V)))).symm

/-- The graph on `V` whose edges are exactly `S`. Reducible, so decidability instances fire. -/
abbrev ofEdges (S : Finset (Sym2 V)) : SimpleGraph V :=
  fromEdgeSet (S : Set (Sym2 V))

/-- The probability weight of the configuration in which exactly the edges of `S ⊆ E` are open,
each edge `e` being retained independently with probability `w e`. -/
def weight (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (S : Finset (Sym2 V)) : ℚ :=
  (∏ e ∈ S, w e) * (∏ e ∈ E \ S, (1 - w e))

/-- The probability of an event described by a decidable predicate on the open edge-set. -/
def probOf (E : Finset (Sym2 V)) (w : Sym2 V → ℚ)
    (ev : Finset (Sym2 V) → Prop) [DecidablePred ev] : ℚ :=
  ∑ S ∈ E.powerset, if ev S then weight E w S else 0

/-- `connProb E w u v` is the probability that `u` and `v` are connected in the weighted
Bernoulli bond percolation on the graph with edge set `E`. -/
def connProb (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (u v : V) : ℚ :=
  probOf E w (fun S => (ofEdges S).Reachable u v)

/-- Uniform retention probability `p` on every edge. -/
abbrev connProbU (E : Finset (Sym2 V)) (p : ℚ) (u v : V) : ℚ :=
  connProb E (fun _ => p) u v

/-! ## The bunkbed graph -/

/-- Lift an edge of the base graph into level `i ∈ {0,1}` of the bunkbed. -/
def liftLvl (i : Fin 2) (e : Sym2 V) : Sym2 (V × Fin 2) := e.map (fun x => (x, i))

/-- The bunkbed graph in which the open edges of the lower level are `S₀`, those of the upper
level are `S₁`, and the **posts** over the transversal set `T` are always present. -/
abbrev bbGraph (T : Finset V) (S₀ S₁ : Finset (Sym2 V)) :
    SimpleGraph (V × Fin 2) :=
  ofEdges (S₀.image (liftLvl 0) ∪ S₁.image (liftLvl 1) ∪ T.image (fun x => s((x,0),(x,1))))

/-- Bunkbed percolation: the two levels are percolated **independently** with edge weights `w`,
while every post over `T` is retained. `bbProb E w T x y` is the probability that `x` and `y`
are connected. -/
def bbProb (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (T : Finset V)
    (x y : V × Fin 2) : ℚ :=
  ∑ S₀ ∈ E.powerset, ∑ S₁ ∈ E.powerset,
    (if (bbGraph T S₀ S₁).Reachable x y then 1 else 0) * weight E w S₀ * weight E w S₁

/-- The **bunkbed conjecture** (Kasteleyn 1985; Conjecture 1.1 of the source): for a connected
graph, a transversal set `T`, and `0 < p < 1`, a vertex in the lower level is at least as likely
to be connected to `v` downstairs as to its counterpart `v'` upstairs. -/
def BunkbedConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (E : Finset (Sym2 V)) (T : Finset V) (p : ℚ),
    0 < p → p < 1 → (ofEdges E).Connected → ∀ u v : V,
      bbProb E (fun _ => p) T (u, 0) (v, 0) ≥ bbProb E (fun _ => p) T (u, 0) (v, 1)

/-! ## Partition probabilities of a triple

For the hyperedge-simulation gadget one needs the probabilities of the five ways the
percolation can partition a distinguished triple `a b c` into connected components. -/

/-- `a`, `b`, `c` all in one component. -/
def Pabc (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) : ℚ :=
  probOf E w (fun S => (ofEdges S).Reachable a b ∧ (ofEdges S).Reachable b c)

/-- `b`, `c` together, `a` separate. -/
def Pa_bc (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) : ℚ :=
  probOf E w (fun S => (ofEdges S).Reachable b c ∧ ¬ (ofEdges S).Reachable a b)

/-- `a`, `b` together, `c` separate. -/
def Pab_c (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) : ℚ :=
  probOf E w (fun S => (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable a c)

/-- `a`, `c` together, `b` separate. -/
def Pac_b (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) : ℚ :=
  probOf E w (fun S => (ofEdges S).Reachable a c ∧ ¬ (ofEdges S).Reachable a b)

/-- `a`, `b`, `c` pairwise separated. -/
def Pa_b_c (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) : ℚ :=
  probOf E w (fun S => ¬ (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable b c ∧
    ¬ (ofEdges S).Reachable a c)

/-! ## The hyperedge-simulation gadget `Gₙ` (Fig. 2 of the source)

`Gₙ` has vertices `a = 0` and `v₁, …, vₙ = 1, …, n`. The **spokes** `a–vᵢ` are retained with
probability `1 - P`, and the **path** edges `vᵢ–vᵢ₊₁` with probability `P`. -/

/-- Edge set of the gadget graph `Gₙ`. -/
def gadgetE (n : ℕ) : Finset (Sym2 (Fin (n + 1))) :=
  (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
      (p.1 = 0 ∧ p.2 ≠ 0) ∨ (1 ≤ p.1.val ∧ p.2.val = p.1.val + 1))).image (fun p => s(p.1, p.2))

/-- Edge weights of `Gₙ`: spokes (those meeting `a = 0`) get `1 - P`, path edges get `P`. -/
def gadgetW (n : ℕ) (P : ℚ) (e : Sym2 (Fin (n + 1))) : ℚ :=
  if (0 : Fin (n + 1)) ∈ e then 1 - P else P

end Bunkbed
