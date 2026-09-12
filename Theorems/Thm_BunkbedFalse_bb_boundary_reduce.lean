import Definitions.Def_BunkbedSubstituted
open Bunkbed Bunkbed.Hyper Finset SimpleGraph
namespace BunkbedFalse

/-- **Bunkbed reachability depends only on the per-copy boundary partitions.** If, for every copy
and every level, the open edges of that copy connect its three attachment vertices exactly as the
Wierman-Ziff state prescribes, then reachability between lifted hypergraph vertices in the bunkbed
graph over the substituted graph agrees with reachability in the Wierman-Ziff graph. -/
theorem bb_boundary_reduce (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222)))
    (hsub : ∀ i, S₀ i ⊆ (gadgetE 1204).image (Sym2.map (Bunkbed.Sub.emb i)))
    (hsub' : ∀ i, S₁ i ⊆ (gadgetE 1204).image (Sym2.map (Bunkbed.Sub.emb i)))
    (ψ : Fin 6 × Fin 2 → WZ)
    (hmatch : ∀ (i : Fin 6) (l : Fin 2),
        ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 0) (Bunkbed.Sub.emb i 1)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ab_c))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 1) (Bunkbed.Sub.emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.a_bc))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 0) (Bunkbed.Sub.emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ac_b)))
    (x y : Fin 10) (l : Fin 2) :
    (bbGraph Bunkbed.Sub.subT (Finset.univ.biUnion S₀) (Finset.univ.biUnion S₁)).Reachable
        (Bunkbed.Sub.iota x, 0) (Bunkbed.Sub.iota y, l)
      ↔ (wzGraph hollomTriple hollomT ψ).Reachable (x, 0) (y, l) := by
  sorry

end BunkbedFalse
