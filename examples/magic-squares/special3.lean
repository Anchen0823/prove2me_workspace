import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3
import Definitions.Def_MagicSquaresSpecial3
import Theorems.Thm_MagicSquares_center_of_order_three

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-! ## Panmagic -/

/-- The only panmagic `3 × 3` square of line sum `3 * e` is the constant square. -/
theorem pan_three_card (e : ℕ) : panMagicCount 3 (3 * e) = 1 := by
  classical
  rw [panMagicCount, panMagicSquares]
  rw [Finset.card_eq_one]
  refine ⟨constSquare3 e, ?_⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨fun i => ?_, fun j => ?_⟩, fun k => ?_, fun k => ?_⟩
    · simp [rowSum, constSquare3]
    · simp [colSum, constSquare3]
    · fin_cases k <;> simp [brokenDiagSum, constSquare3]
    · fin_cases k <;> simp [brokenAntiDiagSum, constSquare3]
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    have hR0 : (M 0 0 : ℕ) + (M 0 1 : ℕ) + (M 0 2 : ℕ) = 3 * e := by
      simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
    have hR1 : (M 1 0 : ℕ) + (M 1 1 : ℕ) + (M 1 2 : ℕ) = 3 * e := by
      simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (1 : Fin 3)
    have hR2 : (M 2 0 : ℕ) + (M 2 1 : ℕ) + (M 2 2 : ℕ) = 3 * e := by
      simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (2 : Fin 3)
    have hC0 : (M 0 0 : ℕ) + (M 1 0 : ℕ) + (M 2 0 : ℕ) = 3 * e := by
      simpa [colSum, Fin.sum_univ_three] using hM.1.2 (0 : Fin 3)
    have hC1 : (M 0 1 : ℕ) + (M 1 1 : ℕ) + (M 2 1 : ℕ) = 3 * e := by
      simpa [colSum, Fin.sum_univ_three] using hM.1.2 (1 : Fin 3)
    have hC2 : (M 0 2 : ℕ) + (M 1 2 : ℕ) + (M 2 2 : ℕ) = 3 * e := by
      simpa [colSum, Fin.sum_univ_three] using hM.1.2 (2 : Fin 3)
    have hB0 : (M 0 0 : ℕ) + (M 1 1 : ℕ) + (M 2 2 : ℕ) = 3 * e := by
      have h := hM.2.1 (0 : Fin 3)
      simpa [brokenDiagSum, Fin.sum_univ_three] using h
    have hB1 : (M 0 1 : ℕ) + (M 1 2 : ℕ) + (M 2 0 : ℕ) = 3 * e := by
      have h := hM.2.1 (1 : Fin 3)
      simpa [brokenDiagSum, Fin.sum_univ_three] using h
    have hB2 : (M 0 2 : ℕ) + (M 1 0 : ℕ) + (M 2 1 : ℕ) = 3 * e := by
      have h := hM.2.1 (2 : Fin 3)
      simpa [brokenDiagSum, Fin.sum_univ_three] using h
    have hA0 : (M 0 2 : ℕ) + (M 1 1 : ℕ) + (M 2 0 : ℕ) = 3 * e := by
      have h := hM.2.2 (0 : Fin 3)
      simpa [brokenAntiDiagSum, Fin.sum_univ_three] using h
    have hA1 : (M 0 0 : ℕ) + (M 1 2 : ℕ) + (M 2 1 : ℕ) = 3 * e := by
      have h := hM.2.2 (1 : Fin 3)
      simpa [brokenAntiDiagSum, Fin.sum_univ_three] using h
    have hA2 : (M 0 1 : ℕ) + (M 1 0 : ℕ) + (M 2 2 : ℕ) = 3 * e := by
      have h := hM.2.2 (2 : Fin 3)
      simpa [brokenAntiDiagSum, Fin.sum_univ_three] using h
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [constSquare3]; omega)

/-! ## Symmetric -/

/-- **Classification of symmetric order-three magic squares.** A symmetric
`3 × 3` magic square of line sum `3 * e` is determined by its top-left corner:
it is `symmMagic3 e (M 0 0)`. Symmetry identifies `M 0 1 = M 1 0`,
`M 0 2 = M 2 0` and `M 1 2 = M 2 1`, leaving five free cells; the anti-diagonal
reads `2 (M 0 2) + (M 1 1) = 3 e` and the rows then determine everything. -/
theorem symmetric_magic_three_classify (e : ℕ) (M : Square 3 ℕ)
    (hM : IsMagic M (3 * e)) (hsym : IsSymmetric M) :
    M = symmMagic3 e (M 0 0) := by
  have hR0 : M 0 0 + M 0 1 + M 0 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
  have hR1 : M 1 0 + M 1 1 + M 1 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (1 : Fin 3)
  have hR2 : M 2 0 + M 2 1 + M 2 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (2 : Fin 3)
  have hD : M 0 0 + M 1 1 + M 2 2 = 3 * e := by
    simpa [diagSum, Fin.sum_univ_three] using hM.2.1
  have hA : M 0 2 + M 1 1 + M 2 0 = 3 * e := by
    simpa [antiDiagSum, Fin.sum_univ_three] using hM.2.2
  have h01 : M 0 1 = M 1 0 := hsym (0 : Fin 3) (1 : Fin 3)
  have h02 : M 0 2 = M 2 0 := hsym (0 : Fin 3) (2 : Fin 3)
  have h12 : M 1 2 = M 2 1 := hsym (1 : Fin 3) (2 : Fin 3)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmMagic3] <;> omega

/-- `symmMagic3 e a` is a magic square of line sum `3 * e` whenever `a` is an
admissible corner parameter. -/
theorem symmMagic3_magic (e a : ℕ) (ha : a ≤ 2 * e) :
    IsMagic (symmMagic3 e a) (3 * e) := by
  refine ⟨⟨fun i => ?_, fun j => ?_⟩, ?_, ?_⟩
  · fin_cases i <;> simp [rowSum, symmMagic3, Fin.sum_univ_three] <;> omega
  · fin_cases j <;> simp [colSum, symmMagic3, Fin.sum_univ_three] <;> omega
  · simp [diagSum, symmMagic3, Fin.sum_univ_three]
    omega
  · simp [antiDiagSum, symmMagic3, Fin.sum_univ_three]
    omega

/-- `symmMagic3 e a` is symmetric for every `a`. -/
theorem symmMagic3_symmetric (e a : ℕ) : IsSymmetric (symmMagic3 e a) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [symmMagic3]

/-- The corner parameter enumerates the symmetric order-three magic squares of
line sum `3 * e`. -/
theorem symm_three_bij (e : ℕ) :
    symmetricMagicCount 3 (3 * e) = symmParamCount e := by
  classical
  rw [symmetricMagicCount, symmParamCount, symmParamSet]
  change
    (Finset.univ.filter (fun M : Square 3 (Fin (3 * e + 1)) =>
      IsMagic (fun i j => (M i j : ℕ)) (3 * e) ∧
        IsSymmetric (fun i j => (M i j : ℕ)))).card =
    (Finset.range (2 * e + 1)).card
  refine Finset.card_bij (fun M _ => (M 0 0 : ℕ)) ?h_mem ?h_inj ?h_surj
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    simp only [Finset.mem_range]
    have hEq := symmetric_magic_three_classify e (fun i j => (M i j : ℕ)) hM.1 hM.2
    have hR0 : (M 0 0 : ℕ) + (M 0 1 : ℕ) + (M 0 2 : ℕ) = 3 * e := by
      simpa [rowSum, Fin.sum_univ_three] using hM.1.1.1 (0 : Fin 3)
    have h01 : (M 0 1 : ℕ) = 2 * e - (M 0 0 : ℕ) := by
      have h := congr_fun (congr_fun hEq (0 : Fin 3)) (1 : Fin 3)
      simpa [symmMagic3] using h
    have h02 : (M 0 2 : ℕ) = e := by
      have h := congr_fun (congr_fun hEq (0 : Fin 3)) (2 : Fin 3)
      simpa [symmMagic3] using h
    omega
  · intro M₁ hM₁ M₂ hM₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM₁ hM₂
    have hEq₁ := symmetric_magic_three_classify e (fun i j => (M₁ i j : ℕ)) hM₁.1 hM₁.2
    have hEq₂ := symmetric_magic_three_classify e (fun i j => (M₂ i j : ℕ)) hM₂.1 hM₂.2
    have ha : (M₁ 0 0 : ℕ) = (M₂ 0 0 : ℕ) := heq
    ext i j
    calc
      (M₁ i j : ℕ) = symmMagic3 e (M₁ 0 0 : ℕ) i j := by
        exact congr_fun (congr_fun hEq₁ i) j
      _ = symmMagic3 e (M₂ 0 0 : ℕ) i j := by rw [ha]
      _ = (M₂ i j : ℕ) := by
        exact (congr_fun (congr_fun hEq₂ i) j).symm
  · intro a ha
    simp only [Finset.mem_range] at ha
    have ha' : a ≤ 2 * e := by omega
    let M : Square 3 (Fin (3 * e + 1)) :=
      fun i j => ⟨symmMagic3 e a i j, by
        fin_cases i <;> fin_cases j <;> simp [symmMagic3] <;> omega⟩
    refine ⟨M, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · have : (fun i j => (M i j : ℕ)) = symmMagic3 e a := by
          ext i j
          simp [M]
        rw [this]
        exact symmMagic3_magic e a ha'
      · have : (fun i j => (M i j : ℕ)) = symmMagic3 e a := by
          ext i j
          simp [M]
        rw [this]
        exact symmMagic3_symmetric e a
    · simp [M, symmMagic3]
