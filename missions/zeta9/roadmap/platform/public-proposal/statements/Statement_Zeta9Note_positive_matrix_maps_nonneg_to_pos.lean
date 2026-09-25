import Mathlib

namespace Zeta9Note

theorem positive_matrix_maps_nonneg_to_pos
    (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : ∀ i j : Fin 5, 0 < M i j)
    (v : Fin 5 → ℝ) (hv : v ≠ 0) (hvnn : ∀ i : Fin 5, 0 ≤ v i) :
    ∀ i : Fin 5, 0 < M.mulVec v i := by sorry

end Zeta9Note
