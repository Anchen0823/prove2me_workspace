import Definitions.Def_BunkbedPercolation

/-!
# Hypergraph percolation, Hollom's example, and the Wierman–Ziff model

Section 3 of Gladkov–Pak–Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025) e2420725122.
-/

namespace Bunkbed.Hyper

open Bunkbed SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The underlying vertex set of an ordered hyperedge `(a,b,c)`. -/
def tripleSet (t : V × V × V) : Finset V := {t.1, t.2.1, t.2.2}

/-- All edges of the clique on `s`, placed at level `l` of the bunkbed. -/
def cliqueAt (s : Finset V) (l : Fin 2) : Finset (Sym2 (V × Fin 2)) :=
  ((s ×ˢ s).filter (fun p => p.1 ≠ p.2)).image (fun p => s((p.1, l), (p.2, l)))

/-- The vertical posts over the transversal set `T`; these are always retained. -/
def posts (T : Finset V) : Finset (Sym2 (V × Fin 2)) := T.image (fun t => s((t, 0), (t, 1)))

/-! ## Alternative bunkbed hypergraph percolation -/

/-- In the **alternative** model each hyperedge `i` is retained on exactly one of the two
levels — `σ i` — and deleted on the other. Posts over `T` are always present. -/
abbrev altBBGraph {ι : Type*} [Fintype ι] (e : ι → Finset V) (T : Finset V) (σ : ι → Fin 2) :
    SimpleGraph (V × Fin 2) :=
  ofEdges ((Finset.univ.biUnion (fun i => cliqueAt (e i) (σ i))) ∪ posts T)

/-- `ℙᵃˡᵗ[x ↔ y]`: all `2^{|ι|}` level-assignments are equally likely. -/
def altProb {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → Finset V) (T : Finset V)
    (x y : V × Fin 2) : ℚ :=
  (∑ σ : ι → Fin 2, if (altBBGraph e T σ).Reachable x y then (1 : ℚ) else 0)
    / 2 ^ Fintype.card ι

/-! ## Hollom's 3-uniform hypergraph (Fig. 1)

Ordered as in the path `ρ` of Eq. [5], so that in each hyperedge `(a,b,c)` the first vertex
`a` is the transversal one. Vertices `uᵢ ↦ i-1`, so `u₁ = 0`, …, `u₁₀ = 9`. -/
def hollomTriple : Fin 6 → (Fin 10 × Fin 10 × Fin 10) :=
  ![(1, 0, 2), (8, 2, 5), (6, 5, 4), (1, 4, 3), (6, 3, 7), (8, 7, 9)]

/-- The six hyperedges of Hollom's hypergraph, as vertex sets. -/
def hollomE (i : Fin 6) : Finset (Fin 10) := tripleSet (hollomTriple i)

/-- Hollom's transversal set `T = {u₂, u₇, u₉}`. -/
def hollomT : Finset (Fin 10) := {1, 6, 8}

/-! ## The Wierman–Ziff five-state model -/

/-- The five states of a hyperedge `(a,b,c)` in the WZ model: which of its vertices the
hyperedge connects. -/
inductive WZ | abc | ab_c | ac_b | a_bc | a_b_c
  deriving DecidableEq, Repr

instance : Fintype WZ := ⟨{.abc, .ab_c, .ac_b, .a_bc, .a_b_c}, by intro x; cases x <;> decide⟩

/-- The pairs of vertices that state `s` links, for the hyperedge `t = (a,b,c)` at level `l`. -/
def WZ.edges (s : WZ) (t : V × V × V) (l : Fin 2) : Finset (Sym2 (V × Fin 2)) :=
  let a : V × Fin 2 := (t.1, l)
  let b : V × Fin 2 := (t.2.1, l)
  let c : V × Fin 2 := (t.2.2, l)
  match s with
  | .abc   => {s(a, b), s(b, c), s(a, c)}
  | .ab_c  => {s(a, b)}
  | .ac_b  => {s(a, c)}
  | .a_bc  => {s(b, c)}
  | .a_b_c => ∅

/-- The graph realised by a WZ configuration `ψ`, which assigns a state to each hyperedge on
each of the two levels. Posts over `T` are always present. -/
abbrev wzGraph {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → (V × V × V)) (T : Finset V)
    (ψ : ι × Fin 2 → WZ) : SimpleGraph (V × Fin 2) :=
  ofEdges ((Finset.univ.biUnion (fun p : ι × Fin 2 => (ψ p).edges (t p.1) p.2)) ∪ posts T)

/-- `ℙʷᶻ[x ↔ y]`, where each hyperedge on each level independently takes state `s` with
probability `P s`.

⚠️ This carries **no internal normalisation**: `P` is an arbitrary `WZ → ℚ`, so the total mass
is `(∑ s, P s) ^ (2 * |ι|)`. Comparing two values of `wzProb` is only meaningful when the caller
supplies a genuine distribution, i.e. `0 ≤ P s` for every `s` and `∑ s, P s = 1`. (Contrast
`altProb`, which normalises internally and always lands in `[0,1]`.) -/
def wzProb {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → (V × V × V)) (T : Finset V)
    (P : WZ → ℚ) (x y : V × Fin 2) : ℚ :=
  ∑ ψ : ι × Fin 2 → WZ,
    (if (wzGraph t T ψ).Reachable x y then (1 : ℚ) else 0) * ∏ p : ι × Fin 2, P (ψ p)

end Bunkbed.Hyper
