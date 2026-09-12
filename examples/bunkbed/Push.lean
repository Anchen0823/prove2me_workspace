import Mathlib

open Finset

namespace Push

variable {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
variable {A : I → Type*} [∀ i, DecidableEq (A i)]

theorem pi_pushforward_sum
    (D : ∀ i, Finset (A i)) (st : ∀ i, A i → B) (mu : ∀ i, A i → ℚ)
    (P : I → B → ℚ)
    (hmass : ∀ i b, ∑ a ∈ D i with st i a = b, mu i a = P i b)
    (F : (I → B) → ℚ) :
    (∑ a ∈ Fintype.piFinset D, F (fun i => st i (a i)) * ∏ i, mu i (a i)) =
      ∑ b : I → B, F b * ∏ i, P i (b i) := by
  classical
  let q : (∀ i, A i) → (I → B) := fun a i => st i (a i)
  calc
    _ = ∑ b : I → B, ∑ a ∈ Fintype.piFinset D with q a = b,
          F (q a) * ∏ i, mu i (a i) := by
      rw [Finset.sum_fiberwise (Fintype.piFinset D) q
        (fun a => F (q a) * ∏ i, mu i (a i))]
    _ = ∑ b : I → B, F b * ∏ i, P i (b i) := by
      apply Finset.sum_congr rfl
      intro b _
      have hpi :
          (Fintype.piFinset (fun i => (D i).filter (fun a => st i a = b i))) =
            (Fintype.piFinset D).filter (fun a => q a = b) := by
        ext a
        simp only [Fintype.mem_piFinset, mem_filter, q]
        constructor
        · intro h
          exact ⟨fun i => (h i).1, funext fun i => (h i).2⟩
        · rintro ⟨hD, hq⟩ i
          exact ⟨hD i, congrFun hq i⟩
      rw [← hpi]
      have hF : ∀ a ∈ Fintype.piFinset (fun i => (D i).filter (fun x => st i x = b i)),
          F (q a) = F b := by
        intro a ha
        congr 1
        funext i
        exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp ha i)).2
      rw [Finset.sum_congr rfl (fun a ha => by rw [hF a ha]), ← Finset.mul_sum]
      rw [← Finset.prod_univ_sum]
      simp_rw [hmass]

end Push
