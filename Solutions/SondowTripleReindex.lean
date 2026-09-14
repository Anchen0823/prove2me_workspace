import Mathlib.Tactic

open Finset

namespace EulerMascheroni.Sondow

theorem triangle_interval_sum_reindex (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range (n+1), ∑ i ∈ range j, ∑ k ∈ Icc (i+1) j, f i j k) =
      ∑ k ∈ Icc 1 n, ∑ i ∈ range k, ∑ j ∈ Ico k (n+1), f i j k := by
  have hleft (j : ℕ) : (∑ i ∈ range j, ∑ k ∈ Icc (i+1) j, f i j k) =
      ∑ p ∈ (range j).sigma (fun i => Icc (i+1) j), f p.1 j p.2 := sum_sigma' ..
  have hright (k : ℕ) : (∑ i ∈ range k, ∑ j ∈ Ico k (n+1), f i j k) =
      ∑ p ∈ (range k).sigma (fun _ => Ico k (n+1)), f p.1 p.2 k := sum_sigma' ..
  simp_rw [hleft, hright]
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2.2, ⟨x.2.1, x.1⟩⟩)
    (fun x => ⟨x.2.2, ⟨x.2.1, x.1⟩⟩) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) <;>
    simp only [mem_sigma, mem_range, mem_Icc, mem_Ico, Sigma.forall] <;> omega

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.triangle_interval_sum_reindex
