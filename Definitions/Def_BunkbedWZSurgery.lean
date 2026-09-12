import Definitions.Def_BunkbedWZRefined

/-!
# The path surgery of the involution argument

Section 3.5 of Gladkov-Pak-Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025)
e2420725122.

The involution used to prove the robustness lemma is built from the path `ρ` of Eq. [5], which
traverses every hyperedge of Hollom's hypergraph exactly once and avoids the transversal
vertices. Along `ρ` the non-transversal vertices appear in the order `hollomPath`, and hyperedge
`i` is the triple `(hollomTr i, hollomPath i, hollomPath (i+1))` -- transversal vertex first.

Given a refined configuration `Ψ` and the first hyperedge `e` along `ρ` whose state lies in
`Λ²₊`, the involution `phiExt` leaves the hyperedges before `e` alone, applies the
half-reflection `eta` at `e`, and applies the level swap `rho` to every hyperedge after `e`.
Correspondingly `surgeryMap` reflects the level of every non-transversal vertex lying strictly
beyond `e` along `ρ`, fixing the transversal vertices and everything before `e`.

Note that transversal vertices are deliberately *not* reflected: each of them serves two
hyperedges, one before and one after `e`, so no consistent assignment is possible. The resulting
mismatch is harmless because the posts over the transversal set are always present, so a
transversal vertex is always connected to its own counterpart on the other level.
-/

namespace Bunkbed.Hyper

/-- The non-transversal vertices of Hollom's hypergraph, in the order they appear along the
path `ρ` of Eq. [5]: `u₁, u₃, u₆, u₅, u₄, u₈, u₁₀`. -/
def hollomPath : Fin 7 → Fin 10 := ![0, 2, 5, 4, 3, 7, 9]

/-- The transversal vertex of each hyperedge of Hollom's hypergraph, in the order of `ρ`. -/
def hollomTr : Fin 6 → Fin 10 := ![1, 8, 6, 1, 6, 8]

/-- Exchange the two levels of the bunkbed. -/
def lvlSwap : Fin 2 → Fin 2 := fun l => if l = 0 then 1 else 0

/-- The vertices whose level the surgery reflects: the non-transversal vertices lying strictly
beyond hyperedge `e` along `ρ`. Transversal vertices are never reflected. -/
def reflected (e : Fin 6) (v : Fin 10) : Bool :=
  decide (∃ j : Fin 7, hollomPath j = v ∧ e.val < j.val)

/-- The vertex map of the path surgery. -/
def surgeryMap (e : Fin 6) (x : Fin 10 × Fin 2) : Fin 10 × Fin 2 :=
  if reflected e x.1 then (x.1, lvlSwap x.2) else x

/-- The underlying Wierman-Ziff configuration of a refined configuration: the first component of
a refined state is the lower-level state, the second the upper-level one. -/
def wzOfExt (Ψ : Fin 6 → WZExt) : Fin 6 × Fin 2 → WZ :=
  fun p => if p.2 = 0 then (WZExt.toPair (Ψ p.1)).1 else (WZExt.toPair (Ψ p.1)).2

/-- The composite involution `φ` of Section 3.5: leave the hyperedges before `e` alone, apply the
half-reflection at `e`, and apply the level swap to every hyperedge after `e`. -/
def phiExt (e : Fin 6) (Ψ : Fin 6 → WZExt) : Fin 6 → WZExt :=
  fun h => if h.val < e.val then Ψ h else if h = e then WZExt.eta (Ψ h) else WZExt.rho (Ψ h)

end Bunkbed.Hyper

