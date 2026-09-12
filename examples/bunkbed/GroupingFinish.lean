import examples.bunkbed.GroupingCore
open Bunkbed Bunkbed.Hyper Bunkbed.Sub Finset SimpleGraph Function
set_option maxRecDepth 2000
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
  apply BunkbedFalse.bb_boundary_reduce S₀ S₁
  · intro i
    have hi := Fintype.mem_piFinset.mp hS₀ i
    exact Finset.mem_powerset.mp hi
  · intro i
    have hi := Fintype.mem_piFinset.mp hS₁ i
    exact Finset.mem_powerset.mp hi
  · exact selected_state_match S₀ S₁

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
  classical
  let E : Fin 6 → Finset (Sym2 (Fin 7222)) :=
    fun i => (gadgetE 1204).image (Sym2.map (emb i))
  let D := Fintype.piFinset (fun i : Fin 6 => (E i).powerset)
  let mu : (i : Fin 6) → Finset (Sym2 (Fin 7222)) → ℚ :=
    fun i S => weight (E i) (fun _ => (1/2 : ℚ)) S
  let C : (Fin 6 × Fin 2 → WZ) → ℚ := fun ψ =>
    if (wzGraph hollomTriple hollomT ψ).Reachable (x, 0) (y, l) then 1 else 0
  have hfactor :
      bbProb subEdges (fun _ => (1/2 : ℚ)) subT (iota x, 0) (iota y, l) =
        ∑ S₀ ∈ D, ∑ S₁ ∈ D,
          (if (bbGraph subT (Finset.univ.biUnion S₀)
              (Finset.univ.biUnion S₁)).Reachable (iota x, 0) (iota y, l) then 1 else 0) *
            (∏ i, mu i (S₀ i)) * ∏ i, mu i (S₁ i) := by
    simpa only [subEdges, E, D, mu] using
      BunkbedAux.bbProb_biUnion_disjoint E hdisj (fun _ => (1/2 : ℚ)) subT
        (iota x, 0) (iota y, l)
  rw [hfactor]
  have hreduce :
      (∑ S₀ ∈ D, ∑ S₁ ∈ D,
          (if (bbGraph subT (Finset.univ.biUnion S₀)
              (Finset.univ.biUnion S₁)).Reachable (iota x, 0) (iota y, l) then 1 else 0) *
            (∏ i, mu i (S₀ i)) * ∏ i, mu i (S₁ i)) =
        ∑ S₀ ∈ D, ∑ S₁ ∈ D,
          C (twoLevel (copyStates S₀, copyStates S₁)) *
            (∏ i, mu i (S₀ i)) * ∏ i, mu i (S₁ i) := by
    apply Finset.sum_congr rfl
    intro S₀ hS₀
    apply Finset.sum_congr rfl
    intro S₁ hS₁
    apply congrArg (fun q : ℚ => q * (∏ i, mu i (S₀ i)) * ∏ i, mu i (S₁ i))
    apply if_congr
    · exact configuration_reach S₀ S₁ (by simpa [D, E] using hS₀)
        (by simpa [D, E] using hS₁) x y l
    · rfl
    · rfl
  rw [hreduce]
  have hpush₁ :
      (∑ S₀ ∈ D, ∑ S₁ ∈ D,
          C (twoLevel (copyStates S₀, copyStates S₁)) *
            (∏ i, mu i (S₀ i)) * ∏ i, mu i (S₁ i)) =
        ∑ S₀ ∈ D, ∑ φ₁ : Fin 6 → WZ,
          (C (twoLevel (copyStates S₀, φ₁)) * ∏ i, mu i (S₀ i)) *
            ∏ i, P (φ₁ i) := by
    apply Finset.sum_congr rfl
    intro S₀ hS₀
    simpa only [D, E, mu, copyStates] using
      one_level_push P habc hab hac hbc hsep
        (fun φ₁ => C (twoLevel (copyStates S₀, φ₁)) * ∏ i, mu i (S₀ i))
  rw [hpush₁]
  have hpush₀ :
      (∑ S₀ ∈ D, ∑ φ₁ : Fin 6 → WZ,
          (C (twoLevel (copyStates S₀, φ₁)) * ∏ i, mu i (S₀ i)) *
            ∏ i, P (φ₁ i)) =
        ∑ φ₀ : Fin 6 → WZ, ∑ φ₁ : Fin 6 → WZ,
          C (twoLevel (φ₀, φ₁)) * (∏ i, P (φ₀ i)) * ∏ i, P (φ₁ i) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ φ₁ : Fin 6 → WZ, ∑ φ₀ : Fin 6 → WZ,
            (C (twoLevel (φ₀, φ₁)) * ∏ i, P (φ₁ i)) *
              ∏ i, P (φ₀ i) := by
        apply Finset.sum_congr rfl
        intro φ₁ _
        simpa only [D, E, mu, copyStates] using
          one_level_push P habc hab hac hbc hsep
            (fun φ₀ => C (twoLevel (φ₀, φ₁)) * ∏ i, P (φ₁ i))
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro φ₀ _
        apply Finset.sum_congr rfl
        intro φ₁ _
        ring
  rw [hpush₀]
  unfold wzProb C
  rw [← Fintype.sum_prod_type]
  refine Fintype.sum_equiv twoLevelEquiv _ _ ?_
  rintro ⟨φ₀, φ₁⟩
  rw [twoLevel_prod]

