import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3
import Theorems.Thm_MagicSquares_magic_three_param_sufficient
import Theorems.Thm_MagicSquares_magic_three_param_necessary

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

namespace MagicSquares

-- The bijection: M  ->  (M 0 0, M 0 2)
theorem magic_three_param_bij_proof (e : ℕ) : magicCount 3 (3 * e) = paramCount e := by
  classical
  simp only [magicCount, paramCount]
  change
    (Finset.univ.filter (fun M : Square 3 (Fin (3 * e + 1)) =>
      IsMagic (fun i j => (M i j : ℕ)) (3 * e))).card =
    (((Finset.range (2 * e + 1)).product (Finset.range (2 * e + 1))).filter
      (fun ac => IsParam3 e ac.1 ac.2)).card
  refine Finset.card_bij (fun M _hM => ((M 0 0 : ℕ), (M 0 2 : ℕ))) ?h_mem ?h_inj ?h_surj
  · -- (1) the image of a magic square is an admissible parameter pair
    intro M hM
    simp at hM
    simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    have hEq :=
      magic_three_param_necessary e ((fun i j => (M i j : ℕ)) : Square 3 ℕ)
        (by simpa using hM)
    have h11 : (M 1 1 : ℕ) = e := by
      have := congr_fun (congr_fun hEq (1 : Fin 3)) (1 : Fin 3)
      simpa [mkMagic3] using this
    have hD : (M 0 0 : ℕ) + (M 1 1 : ℕ) + (M 2 2 : ℕ) = 3 * e := by
      simpa [diagSum, Fin.sum_univ_three] using hM.2.1
    have hA : (M 0 2 : ℕ) + (M 1 1 : ℕ) + (M 2 0 : ℕ) = 3 * e := by
      simpa [antiDiagSum, Fin.sum_univ_three] using hM.2.2
    have hR0 : (M 0 0 : ℕ) + (M 0 1 : ℕ) + (M 0 2 : ℕ) = 3 * e := by
      simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
    have hR1 : (M 1 0 : ℕ) + (M 1 1 : ℕ) + (M 1 2 : ℕ) = 3 * e := by
      simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (1 : Fin 3)
    have hC0 : (M 0 0 : ℕ) + (M 1 0 : ℕ) + (M 2 0 : ℕ) = 3 * e := by
      simpa [colSum, Fin.sum_univ_three] using hM.1.2 (0 : Fin 3)
    have hC1 : (M 0 1 : ℕ) + (M 1 1 : ℕ) + (M 2 1 : ℕ) = 3 * e := by
      simpa [colSum, Fin.sum_univ_three] using hM.1.2 (1 : Fin 3)
    have hC2 : (M 0 2 : ℕ) + (M 1 2 : ℕ) + (M 2 2 : ℕ) = 3 * e := by
      simpa [colSum, Fin.sum_univ_three] using hM.1.2 (2 : Fin 3)
    have h01 : (M 0 1 : ℕ) = 3 * e - (M 0 0 : ℕ) - (M 0 2 : ℕ) := by
      have := congr_fun (congr_fun hEq (0 : Fin 3)) (1 : Fin 3)
      simpa [mkMagic3] using this
    have h10 : (M 1 0 : ℕ) = e + (M 0 2 : ℕ) - (M 0 0 : ℕ) := by
      have := congr_fun (congr_fun hEq (1 : Fin 3)) (0 : Fin 3)
      simpa [mkMagic3] using this
    have h12 : (M 1 2 : ℕ) = e + (M 0 0 : ℕ) - (M 0 2 : ℕ) := by
      have := congr_fun (congr_fun hEq (1 : Fin 3)) (2 : Fin 3)
      simpa [mkMagic3] using this
    have h21 : (M 2 1 : ℕ) = (M 0 0 : ℕ) + (M 0 2 : ℕ) - e := by
      have := congr_fun (congr_fun hEq (2 : Fin 3)) (1 : Fin 3)
      simpa [mkMagic3] using this
    have ha_le : (M 0 0 : ℕ) ≤ 2 * e := by omega
    have hc_le : (M 0 2 : ℕ) ≤ 2 * e := by omega
    have h1 : e ≤ (M 0 0 : ℕ) + (M 0 2 : ℕ) := by omega
    have h2 : (M 0 0 : ℕ) + (M 0 2 : ℕ) ≤ 3 * e := by omega
    have h3 : (M 0 0 : ℕ) ≤ e + (M 0 2 : ℕ) := by omega
    have h4 : (M 0 2 : ℕ) ≤ e + (M 0 0 : ℕ) := by omega
    exact ⟨⟨ha_le, hc_le⟩, ⟨h1, h2, h3, h4⟩⟩
  · -- (2) injectivity: a square is determined by its two top corners
    intro M₁ hM₁ M₂ hM₂ heq
    simp at hM₁ hM₂
    have ha : (M₁ 0 0 : ℕ) = (M₂ 0 0 : ℕ) := by
      simpa using congrArg Prod.fst heq
    have hc : (M₁ 0 2 : ℕ) = (M₂ 0 2 : ℕ) := by
      simpa using congrArg Prod.snd heq
    have hEq₁ : ((fun i j => (M₁ i j : ℕ)) : Square 3 ℕ) =
        mkMagic3 e (M₁ 0 0 : ℕ) (M₁ 0 2 : ℕ) :=
      magic_three_param_necessary e ((fun i j => (M₁ i j : ℕ)) : Square 3 ℕ)
        (by simpa using hM₁)
    have hEq₂ : ((fun i j => (M₂ i j : ℕ)) : Square 3 ℕ) =
        mkMagic3 e (M₂ 0 0 : ℕ) (M₂ 0 2 : ℕ) :=
      magic_three_param_necessary e ((fun i j => (M₂ i j : ℕ)) : Square 3 ℕ)
        (by simpa using hM₂)
    ext i j
    calc
      (M₁ i j : ℕ) = (mkMagic3 e (M₁ 0 0 : ℕ) (M₁ 0 2 : ℕ)) i j := by
        exact congr_fun (congr_fun hEq₁ i) j
      _ = (mkMagic3 e (M₂ 0 0 : ℕ) (M₂ 0 2 : ℕ)) i j := by
        rw [ha, hc]
      _ = (M₂ i j : ℕ) := by
        exact (congr_fun (congr_fun hEq₂ i) j).symm
  · -- (3) surjectivity: every admissible pair comes from a magic square
    intro ac hac
    simp at hac
    rcases ac with ⟨a, c⟩
    simp at hac
    rcases hac with ⟨⟨ha_lt, hc_lt⟩, hparam⟩
    let M : Square 3 (Fin (3 * e + 1)) :=
      fun i j => ⟨(mkMagic3 e a c) i j, by
        fin_cases i <;> fin_cases j <;> simp [mkMagic3] <;> omega⟩
    refine ⟨M, ?_, ?_⟩
    · simp
      simpa [M] using magic_three_param_sufficient e a c hparam
    · simp [M, mkMagic3]

end MagicSquares
