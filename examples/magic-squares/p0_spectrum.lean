import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresPandiagonal
import Theorems.Thm_MagicSquares_pan_three_card
import Theorems.Thm_MagicSquares_pan_three_otherwise

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-! ## Order two

A `2 × 2` semi-magic square of line sum `t` is `[[a, t-a], [t-a, a]]` with
`0 ≤ a ≤ t`; adding the two main diagonals forces `2 a = t`. -/

/-- Structure of a `2 × 2` semi-magic square of line sum `t`. -/
private lemma two_structure (t : ℕ) (M : Square 2 ℕ) (hM : IsSemiMagic M t) :
    M 0 1 = t - M 0 0 ∧ M 1 0 = t - M 0 0 ∧ M 1 1 = M 0 0 := by
  have hR0 : M 0 0 + M 0 1 = t := by simpa [rowSum] using hM.1 (0 : Fin 2)
  have hR1 : M 1 0 + M 1 1 = t := by simpa [rowSum] using hM.1 (1 : Fin 2)
  have hC0 : M 0 0 + M 1 0 = t := by simpa [colSum] using hM.2 (0 : Fin 2)
  have hC1 : M 0 1 + M 1 1 = t := by simpa [colSum] using hM.2 (1 : Fin 2)
  omega

/-- `H_2(t) = t + 1` (BCCG 2003, §2). -/
theorem semi_magic_count_two (t : ℕ) : semiMagicCount 2 t = t + 1 := by
  classical
  rw [semiMagicCount, semiMagicSquares]
  have hbij : (Finset.univ.filter (fun M : Square 2 (Fin (t + 1)) =>
        IsSemiMagic (fun i j => (M i j : ℕ)) t)).card = (Finset.range (t + 1)).card := by
    refine Finset.card_bij (fun M _ => (M 0 0 : ℕ)) ?_ ?_ ?_
    · intro M _hM
      simp only [Finset.mem_range]
      exact (M 0 0).isLt
    · intro M₁ hM₁ M₂ hM₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM₁ hM₂
      obtain ⟨h₁a, h₁b, h₁c⟩ := two_structure t (fun i j => (M₁ i j : ℕ)) hM₁
      obtain ⟨h₂a, h₂b, h₂c⟩ := two_structure t (fun i j => (M₂ i j : ℕ)) hM₂
      have e00 : (M₁ 0 0 : ℕ) = (M₂ 0 0 : ℕ) := heq
      have e01 : (M₁ 0 1 : ℕ) = (M₂ 0 1 : ℕ) := by omega
      have e10 : (M₁ 1 0 : ℕ) = (M₂ 1 0 : ℕ) := by omega
      have e11 : (M₁ 1 1 : ℕ) = (M₂ 1 1 : ℕ) := by omega
      have hall : ∀ i j : Fin 2, (M₁ i j : ℕ) = (M₂ i j : ℕ) := by
        intro i j
        fin_cases i <;> fin_cases j
        · exact e00
        · exact e01
        · exact e10
        · exact e11
      funext i j
      exact Fin.ext (hall i j)
    · intro a ha
      simp only [Finset.mem_range] at ha
      let M : Square 2 (Fin (t + 1)) :=
        ![![⟨a, by omega⟩, ⟨t - a, by omega⟩], ![⟨t - a, by omega⟩, ⟨a, by omega⟩]]
      refine ⟨M, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun i => ?_, fun j => ?_⟩
        · fin_cases i <;> simp [rowSum, Fin.sum_univ_two, M] <;> omega
        · fin_cases j <;> simp [colSum, Fin.sum_univ_two, M] <;> omega
      · simp [M]
  rw [hbij, Finset.card_range]

/-- `M_2(t) = 1` if `t` is even and `0` otherwise (BCCG 2003, §2). -/
theorem magic_count_two (t : ℕ) : magicCount 2 t = if 2 ∣ t then 1 else 0 := by
  classical
  rw [magicCount, magicSquares]
  by_cases h : 2 ∣ t
  · obtain ⟨e, rfl⟩ := h
    let C : Square 2 (Fin (2 * e + 1)) := fun _ _ => ⟨e, by omega⟩
    rw [if_pos (dvd_mul_right 2 e), Finset.card_eq_one]
    refine ⟨C, ?_⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨fun i => ?_, fun j => ?_⟩, ?_, ?_⟩
      · fin_cases i <;> simp [rowSum, C]
      · fin_cases j <;> simp [colSum, C]
      · simp [diagSum, C]
      · simp [antiDiagSum, C]
    · intro M hM
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
      obtain ⟨hsa, hsb, hsc⟩ := two_structure (2 * e) (fun i j => (M i j : ℕ)) hM.1
      have hD : (M 0 0 : ℕ) + (M 1 1 : ℕ) = 2 * e := by
        simpa [diagSum, Fin.sum_univ_two] using hM.2.1
      have hC : ∀ i j : Fin 2, (C i j : ℕ) = e := fun i j => by simp [C]
      have e00 : (M 0 0 : ℕ) = (C 0 0 : ℕ) := by have := hC 0 0; omega
      have e01 : (M 0 1 : ℕ) = (C 0 1 : ℕ) := by have := hC 0 1; omega
      have e10 : (M 1 0 : ℕ) = (C 1 0 : ℕ) := by have := hC 1 0; omega
      have e11 : (M 1 1 : ℕ) = (C 1 1 : ℕ) := by have := hC 1 1; omega
      have hall : ∀ i j : Fin 2, (M i j : ℕ) = (C i j : ℕ) := by
        intro i j
        fin_cases i <;> fin_cases j
        · exact e00
        · exact e01
        · exact e10
        · exact e11
      funext i j
      exact Fin.ext (hall i j)
  · rw [if_neg h, Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨M, hM⟩
    have hm : IsMagic (fun i j : Fin 2 => (M i j : ℕ)) t := by
      simpa [magicSquares] using hM
    obtain ⟨hs1, hs2, hs3⟩ := two_structure t (fun i j => (M i j : ℕ)) hm.1
    have hD : (M 0 0 : ℕ) + (M 1 1 : ℕ) = t := by
      simpa [diagSum, Fin.sum_univ_two] using hm.2.1
    exact h ⟨(M 0 0 : ℕ), by omega⟩

/-- `S_2(t) = M_2(t)`: for order two symmetry is automatic. -/
theorem symmetric_magic_count_two (t : ℕ) :
    symmetricMagicCount 2 t = if 2 ∣ t then 1 else 0 := by
  classical
  have hset : symmetricMagicSquares 2 t = magicSquares 2 t := by
    ext M
    simp only [symmetricMagicSquares, magicSquares, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro h; exact h.1
    · intro h
      refine ⟨h, ?_⟩
      have hR0 : (M 0 0 : ℕ) + (M 0 1 : ℕ) = t := by
        simpa [rowSum] using h.1.1 (0 : Fin 2)
      have hC0 : (M 0 0 : ℕ) + (M 1 0 : ℕ) = t := by
        simpa [colSum] using h.1.2 (0 : Fin 2)
      have h01 : (M 0 1 : ℕ) = (M 1 0 : ℕ) := by omega
      intro i j
      fin_cases i <;> fin_cases j
      · rfl
      · exact h01
      · exact h01.symm
      · rfl
  rw [symmetricMagicCount, hset, ← magicCount, magic_count_two]

/-- `P_2(t) = M_2(t)`: for order two the two notions of broken diagonal coincide. -/
theorem pandiagonal_count_two (t : ℕ) :
    pandiagonalCount 2 t = if 2 ∣ t then 1 else 0 := by
  classical
  have hset : pandiagonalSquares 2 t = magicSquares 2 t := by
    ext M
    simp only [pandiagonalSquares, magicSquares, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro h
      obtain ⟨hsemi, hbd⟩ := h
      exact ⟨hsemi, by simpa [brokenDiagSum, diagSum] using hbd 0,
        by simpa [brokenDiagSum, antiDiagSum] using hbd 1⟩
    · intro h
      refine ⟨h.1, fun k => ?_⟩
      fin_cases k
      · simpa [brokenDiagSum, diagSum] using h.2.1
      · simpa [brokenDiagSum, antiDiagSum] using h.2.2
  rw [pandiagonalCount, hset, ← magicCount, magic_count_two]

/-! ## Order three: the pandiagonal count

Every pandiagonal `3 × 3` square of line sum `t` (in the BCCG sense) is
`M i j = f (i + j)` for a single `f : Fin 3 → ℕ`, and the line sum is
`f 0 + f 1 + f 2`. So the count is the number of triples of naturals summing to `t`. -/

/-- Structure of a pandiagonal `3 × 3` square: the six non-top-row cells are read off
the top row cyclically. -/
private lemma pandiagonal_three_entries (t : ℕ) (M : Square 3 ℕ)
    (hM : IsPandiagonal M t) :
    M 1 0 = M 0 1 ∧ M 1 1 = M 0 2 ∧ M 1 2 = M 0 0 ∧
      M 2 0 = M 0 2 ∧ M 2 1 = M 0 0 ∧ M 2 2 = M 0 1 := by
  obtain ⟨hsemi, hbd⟩ := hM
  have hR0 : M 0 0 + M 0 1 + M 0 2 = t := by
    simpa [rowSum, Fin.sum_univ_three] using hsemi.1 (0 : Fin 3)
  have hR1 : M 1 0 + M 1 1 + M 1 2 = t := by
    simpa [rowSum, Fin.sum_univ_three] using hsemi.1 (1 : Fin 3)
  have hR2 : M 2 0 + M 2 1 + M 2 2 = t := by
    simpa [rowSum, Fin.sum_univ_three] using hsemi.1 (2 : Fin 3)
  have hC0 : M 0 0 + M 1 0 + M 2 0 = t := by
    simpa [colSum, Fin.sum_univ_three] using hsemi.2 (0 : Fin 3)
  have hC1 : M 0 1 + M 1 1 + M 2 1 = t := by
    simpa [colSum, Fin.sum_univ_three] using hsemi.2 (1 : Fin 3)
  have hC2 : M 0 2 + M 1 2 + M 2 2 = t := by
    simpa [colSum, Fin.sum_univ_three] using hsemi.2 (2 : Fin 3)
  have hB0 : M 0 0 + M 1 1 + M 2 2 = t := by
    have h := hbd (0 : Fin 3)
    simpa [brokenDiagSum, Fin.sum_univ_three] using h
  have hB1 : M 0 1 + M 1 2 + M 2 0 = t := by
    have h := hbd (1 : Fin 3)
    simpa [brokenDiagSum, Fin.sum_univ_three] using h
  have hB2 : M 0 2 + M 1 0 + M 2 1 = t := by
    have h := hbd (2 : Fin 3)
    simpa [brokenDiagSum, Fin.sum_univ_three] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- BCCG's `P_3(t) = (t+2).choose 2`. -/
theorem pandiagonal_count_three (t : ℕ) :
    pandiagonalCount 3 t = (t + 2).choose 2 := by
  classical
  rw [pandiagonalCount, pandiagonalSquares]
  have hbij : (Finset.univ.filter (fun M : Square 3 (Fin (t + 1)) =>
        IsPandiagonal (fun i j => (M i j : ℕ)) t)).card =
      ((Finset.range (t + 1)).sigma fun a => Finset.range (t - a + 1)).card := by
    refine Finset.card_bij (fun M _ => ⟨(M 0 1 : ℕ), (M 0 2 : ℕ)⟩) ?_ ?_ ?_
    · intro M hM
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
      simp only [Finset.mem_sigma, Finset.mem_range]
      have hR0 : (M 0 0 : ℕ) + (M 0 1 : ℕ) + (M 0 2 : ℕ) = t := by
        simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
      exact ⟨(M 0 1).isLt, by omega⟩
    · intro M₁ hM₁ M₂ hM₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM₁ hM₂
      have he1 : (M₁ 0 1 : ℕ) = (M₂ 0 1 : ℕ) := congrArg Sigma.fst heq
      have he2 : (M₁ 0 2 : ℕ) = (M₂ 0 2 : ℕ) := congrArg Sigma.snd heq
      have hR0₁ : (M₁ 0 0 : ℕ) + (M₁ 0 1 : ℕ) + (M₁ 0 2 : ℕ) = t := by
        simpa [rowSum, Fin.sum_univ_three] using hM₁.1.1 (0 : Fin 3)
      have hR0₂ : (M₂ 0 0 : ℕ) + (M₂ 0 1 : ℕ) + (M₂ 0 2 : ℕ) = t := by
        simpa [rowSum, Fin.sum_univ_three] using hM₂.1.1 (0 : Fin 3)
      have t0 : (M₁ 0 0 : ℕ) = (M₂ 0 0 : ℕ) := by omega
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
        pandiagonal_three_entries t (fun i j => (M₁ i j : ℕ)) hM₁
      obtain ⟨g₁, g₂, g₃, g₄, g₅, g₆⟩ :=
        pandiagonal_three_entries t (fun i j => (M₂ i j : ℕ)) hM₂
      have hall : ∀ i j : Fin 3, (M₁ i j : ℕ) = (M₂ i j : ℕ) := by
        intro i j
        fin_cases i <;> fin_cases j
        · exact t0
        · exact he1
        · exact he2
        · exact (h₁.trans (he1.trans g₁.symm))
        · exact (h₂.trans (he2.trans g₂.symm))
        · exact (h₃.trans (t0.trans g₃.symm))
        · exact (h₄.trans (he2.trans g₄.symm))
        · exact (h₅.trans (t0.trans g₅.symm))
        · exact (h₆.trans (he1.trans g₆.symm))
      funext i j
      exact Fin.ext (hall i j)
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_range] at hp
      have hsum : p.1 + p.2 ≤ t := by omega
      let g : Fin 3 → ℕ := fun k =>
        if (k : ℕ) = 0 then t - p.1 - p.2 else if (k : ℕ) = 1 then p.1 else p.2
      let M : Square 3 (Fin (t + 1)) := fun i j => ⟨g (i + j), by
        fin_cases i <;> fin_cases j <;> (simp only [g]; split_ifs <;> omega)⟩
      have hMf : ∀ i j : Fin 3, (M i j : ℕ) = g (i + j) := fun i j => rfl
      refine ⟨M, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨fun i => ?_, fun j => ?_⟩, fun k => ?_⟩
        · fin_cases i <;>
            (simp [rowSum, Fin.sum_univ_three, hMf, g]; omega)
        · fin_cases j <;>
            (simp [colSum, Fin.sum_univ_three, hMf, g]; omega)
        · fin_cases k <;>
            (simp [brokenDiagSum, Fin.sum_univ_three, hMf, g]; omega)
      · obtain ⟨a, b⟩ := p
        have h1 : (M 0 1 : ℕ) = a := by
          show g (1 : Fin 3) = a
          simp [g]
        have h2 : (M 0 2 : ℕ) = b := by
          show g (2 : Fin 3) = b
          simp [g]
        simp only [h1, h2]
  rw [hbij, Finset.card_sigma]
  have hstep : ∀ a : ℕ, (Finset.range (t - a + 1)).card = t - a + 1 := fun a =>
    Finset.card_range _
  simp only [hstep]
  rw [show (∑ a ∈ Finset.range (t + 1), (t - a + 1))
      = ∑ a ∈ Finset.range (t + 1), (a + 1) from by
    simpa using (Finset.sum_range_reflect (fun a : ℕ => a + 1) (t + 1))]
  rw [Finset.sum_add_distrib, Finset.sum_range_id, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one, ← Nat.choose_two_right]
  rw [Nat.choose_succ_succ' (t + 1) 1, Nat.choose_one_right, Nat.add_comm]

/-! ## Order three: the two-direction contrast -/

/-- `panMagicCount 3 t = 1` if `3 ∣ t` and `0` otherwise — the two-direction reading,
for contrast with `pandiagonal_count_three`. -/
theorem panmagic_count_three (t : ℕ) : panMagicCount 3 t = if 3 ∣ t then 1 else 0 := by
  by_cases h : 3 ∣ t
  · obtain ⟨e, rfl⟩ := h
    rw [if_pos (dvd_mul_right 3 e)]
    exact pan_three_card e
  · rw [if_neg h]
    exact pan_three_otherwise t h
