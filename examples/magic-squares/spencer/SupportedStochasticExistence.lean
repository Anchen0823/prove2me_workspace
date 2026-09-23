import examples.«magic-squares».spencer.DoublyStochasticSupport
import examples.«magic-squares».spencer.SupportedStochasticPolytope

set_option autoImplicit false

namespace MagicSquaresGeometry

open Finset MagicSquaresBoundary

attribute [local instance] Classical.propDecidable

/-- A supported doubly stochastic matrix can vanish on `S` exactly when a
permutation survives deletion of `S` from the board. -/
theorem supportedStochastic_zeroFace_nonempty_iff_hasPerm (n : ℕ) (hn : 1 ≤ n)
    (B S : Finset (Fin n × Fin n)) :
    {x : (Fin n × Fin n) → ℝ |
      (x ∈ supportedStochasticAffine n B ∧ ∀ e, 0 ≤ x e) ∧
        ∀ e ∈ S, x e = 0}.Nonempty ↔ HasPerm n (B \ S) := by
  classical
  constructor
  · rintro ⟨x, ⟨hx, hxS⟩⟩
    have hM : (fun i j => x (i, j)) ∈ doublyStochastic ℝ (Fin n) :=
      ((mem_supportedStochasticPolytope_iff n B x).mp hx).1
    have hxB : ∀ e ∉ B, x e = 0 :=
      ((mem_supportedStochasticPolytope_iff n B x).mp hx).2
    let T : Finset (Fin n × Fin n) :=
      Finset.univ.filter (fun e => 0 < x e)
    have hT : MatchingCoveredBoard n T :=
      matchingCovered_positive_support n hn (fun i j => x (i, j)) hM
    obtain ⟨e, he⟩ := hT.1
    obtain ⟨σ, _, hσT⟩ := hT.2 e he
    refine ⟨σ, ?_⟩
    intro p hp
    have hpT : p ∈ T := hσT hp
    have hpos : 0 < x p := by simpa [T] using hpT
    have hpB : p ∈ B := by
      by_contra hpB
      rw [hxB p hpB] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    have hpS : p ∉ S := by
      intro hpS
      rw [hxS p hpS] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    exact Finset.mem_sdiff.mpr ⟨hpB, hpS⟩
  · rintro ⟨σ, hσ⟩
    let x : (Fin n × Fin n) → ℝ := fun e => σ.permMatrix ℝ e.1 e.2
    have hmatrix : (fun i j => x (i, j)) ∈ doublyStochastic ℝ (Fin n) := by
      change σ.permMatrix ℝ ∈ doublyStochastic ℝ (Fin n)
      exact permMatrix_mem_doublyStochastic
    have hentry (i j : Fin n) :
        x (i, j) = if σ i = j then 1 else 0 := by
      simp [x, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
        Equiv.toPEquiv_apply, eq_comm]
    have hzero (p : Fin n × Fin n) (hp : p ∉ B \ S) : x p = 0 := by
      rw [hentry]
      split_ifs with hmatch
      · have hpmem : p ∈ permSupport σ := by
          exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, Prod.ext rfl hmatch⟩
        exact False.elim (hp (hσ hpmem))
      · rfl
    have hxB : ∀ p ∉ B, x p = 0 := by
      intro p hpB
      exact hzero p (fun hp => hpB (Finset.mem_sdiff.mp hp).1)
    have hxS : ∀ p ∈ S, x p = 0 := by
      intro p hpS
      exact hzero p (fun hp => (Finset.mem_sdiff.mp hp).2 hpS)
    have hx : x ∈ supportedStochasticAffine n B ∧ ∀ e, 0 ≤ x e :=
      (mem_supportedStochasticPolytope_iff n B x).mpr ⟨hmatrix, hxB⟩
    exact ⟨x, hx, hxS⟩

end MagicSquaresGeometry
