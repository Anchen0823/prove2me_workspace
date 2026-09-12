import examples.bunkbed.GroupingAlgebra
open Bunkbed Bunkbed.Hyper Bunkbed.Sub Finset SimpleGraph Function
set_option maxRecDepth 2000
-- Keep concrete configuration spaces opaque during elaboration.
attribute [local irreducible] Fintype.piFinset gadgetE
set_option maxHeartbeats 200000
namespace Grouping
theorem configuration_reach
    (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222)))
    (hS₀ : S₀ ∈ Fintype.piFinset (fun i : Fin 6 =>
      ((gadgetE 1204).image (Sym2.map (emb i))).powerset))
    (hS₁ : S₁ ∈ Fintype.piFinset (fun i : Fin 6 =>
      ((gadgetE 1204).image (Sym2.map (emb i))).powerset))
    (x y : Fin 10) (l : Fin 2) :
    (bbGraph subT (Finset.univ.biUnion S₀) (Finset.univ.biUnion S₁)).Reachable
        (iota x, 0) (iota y, l) ↔
      (wzGraph hollomTriple hollomT
        (twoLevel (copyStates S₀, copyStates S₁))).Reachable
        (x, 0) (y, l) := by
  exact BunkbedFalse.bb_boundary_reduce S₀ S₁
    (configuration_subset (I := Fin 6) (A := Sym2 (Fin 7222)) (fun i : Fin 6 => (gadgetE 1204).image (Sym2.map (emb i))) S₀ hS₀)
    (configuration_subset (I := Fin 6) (A := Sym2 (Fin 7222)) (fun i : Fin 6 => (gadgetE 1204).image (Sym2.map (emb i))) S₁ hS₁)
    (twoLevel (copyStates S₀, copyStates S₁)) (selected_state_match S₀ S₁) x y l
end Grouping

open Grouping

theorem solution
    (hdisj : ∀ i j : Fin 6, i ≠ j →
      Disjoint ((gadgetE 1204).image (Sym2.map (emb i)))
        ((gadgetE 1204).image (Sym2.map (emb j))))
    (P : WZ → ℚ)
    (habc : P .abc = Pabc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hab : P .ab_c = Pab_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hac : P .ac_b = Pac_b (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hbc : P .a_bc = Pa_bc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hsep : P .a_b_c = Pa_b_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (x y : Fin 10) (l : Fin 2) :
    bbProb subEdges (fun _ => (1/2 : ℚ)) subT (iota x, 0) (iota y, l) =
      wzProb hollomTriple hollomT P (x, 0) (y, l) := by
  let E : Fin 6 → Finset (Sym2 (Fin 7222)) :=
    fun i => (gadgetE 1204).image (Sym2.map (emb i))
  let D := Fintype.piFinset (fun i : Fin 6 => (E i).powerset)
  let mu : (Fin 6 → Finset (Sym2 (Fin 7222))) → ℚ :=
    fun S => ∏ i, weight (E i) (fun _ => (1/2 : ℚ)) (S i)
  let C : (Fin 6 × Fin 2 → WZ) → ℚ := fun ψ =>
    if (wzGraph hollomTriple hollomT ψ).Reachable (x, 0) (y, l) then 1 else 0
  have hpush : ∀ F : (Fin 6 → WZ) → ℚ,
      (∑ S ∈ D, F (copyStates S) * mu S) =
        ∑ φ : Fin 6 → WZ, F φ * ∏ i, P (φ i) := by
    intro F
    exact one_level_push P habc hab hac hbc hsep F
  calc
    _ = ∑ S₀ ∈ D, ∑ S₁ ∈ D,
        (if (bbGraph subT (Finset.univ.biUnion S₀)
          (Finset.univ.biUnion S₁)).Reachable (iota x, 0) (iota y, l) then 1 else 0) *
          mu S₀ * mu S₁ :=
      BunkbedAux.bbProb_biUnion_disjoint E hdisj (fun _ => (1/2 : ℚ)) subT
        (iota x, 0) (iota y, l)
    _ = ∑ S₀ ∈ D, ∑ S₁ ∈ D,
        C (twoLevel (copyStates S₀, copyStates S₁)) * mu S₀ * mu S₁ := by
      exact sum_indicator_congr D mu
        (fun S₀ S₁ => (bbGraph subT (Finset.univ.biUnion S₀)
          (Finset.univ.biUnion S₁)).Reachable (iota x, 0) (iota y, l))
        (fun S₀ S₁ => (wzGraph hollomTriple hollomT
          (twoLevel (copyStates S₀, copyStates S₁))).Reachable (x, 0) (y, l))
        (fun S₀ hS₀ S₁ hS₁ => configuration_reach S₀ S₁ hS₀ hS₁ x y l)
    _ = ∑ φ₀ : Fin 6 → WZ, ∑ φ₁ : Fin 6 → WZ,
        C (twoLevel (φ₀, φ₁)) * (∏ i, P (φ₀ i)) * ∏ i, P (φ₁ i) :=
      push_two D copyStates mu (fun φ => ∏ i, P (φ i)) hpush
        (fun φ₀ φ₁ => C (twoLevel (φ₀, φ₁)))
    _ = _ := pair_state_sum P C



