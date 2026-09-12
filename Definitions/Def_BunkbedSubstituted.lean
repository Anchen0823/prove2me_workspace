import Definitions.Def_BunkbedWZSurgery

/-!
# The substituted graph of Theorem 1.2

Gladkov-Pak-Zimin obtain their counterexample by substituting a copy of the gadget `Gₙ` with
`n = 1204` for each of the six hyperedges of Hollom's hypergraph. The gadget's apex is identified
with the hyperedge's transversal vertex and its two path ends with the hyperedge's two
non-transversal vertices; the remaining `n - 2 = 1202` path vertices of each copy are new and
private to that copy. This yields `10 + 6 * 1202 = 7222` vertices and `6 * (2 * 1204 - 1) = 14442`
edges.

The ten hypergraph vertices sit at `0, …, 9` of `Fin 7222`, and the interior of copy `i` occupies
the block `10 + 1202 * i, …, 10 + 1202 * i + 1201`.
-/

namespace Bunkbed.Sub

open Bunkbed Bunkbed.Hyper SimpleGraph Finset

/-- The ten hypergraph vertices sit at `0, …, 9` of `Fin 7222`. -/
def iota (v : Fin 10) : Fin 7222 := ⟨v.val, by omega⟩

/-- The underlying index map of the copy glued in at hyperedge `i`: the gadget's apex `0` goes to
the transversal vertex, its path ends `1` and `1204` to the two non-transversal vertices, and its
interior to a private block. -/
def embN (i : Fin 6) (k : ℕ) : ℕ :=
  if k = 0 then (hollomTr i).val
  else if k = 1 then (hollomPath i.castSucc).val
  else if k = 1204 then (hollomPath i.succ).val
  else 10 + 1202 * i.val + (k - 2)

lemma embN_lt (i : Fin 6) (k : ℕ) (hk : k < 1205) : embN i k < 7222 := by
  have h1 : i.val < 6 := i.isLt
  have h3 : (hollomTr i).val < 10 := (hollomTr i).isLt
  have h4 : (hollomPath i.castSucc).val < 10 := (hollomPath i.castSucc).isLt
  have h5 : (hollomPath i.succ).val < 10 := (hollomPath i.succ).isLt
  unfold embN
  split_ifs <;> omega

/-- The vertex map of the copy of `G₁₂₀₄` glued in at hyperedge `i`. -/
def emb (i : Fin 6) (k : Fin 1205) : Fin 7222 := ⟨embN i k.val, embN_lt i k.val k.isLt⟩

/-- The edge set of the substituted graph: for each of the six hyperedges of Hollom's hypergraph,
a copy of `G₁₂₀₄` glued in along `emb i`. -/
def subEdges : Finset (Sym2 (Fin 7222)) :=
  Finset.univ.biUnion (fun i : Fin 6 => (gadgetE 1204).image (Sym2.map (emb i)))

/-- The transversal set of the substituted graph: the image of `hollomT = {u₂, u₇, u₉}`. -/
def subT : Finset (Fin 7222) := hollomT.image iota

end Bunkbed.Sub

