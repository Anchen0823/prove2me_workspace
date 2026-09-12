import examples.«five-primes».Theorem51ScaleIntervals

namespace TaoFivePrimes
open Finset

/-- Positive natural odd intervals agree with the public integer interval interface. -/
lemma nat_odd_interval_sum (A B : ℝ) (N : ℕ) (hA : 0 < A) (hB : B ≤ N)
    (F : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, if A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B ∧ n.Coprime 2 then F n else 0) =
      ∑ w ∈ oddRealInterval A B, F w.toNat := by
  classical
  rw [← sum_filter]
  refine sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    have hh := (mem_filter.mp hn).2
    apply (mem_oddRealInterval A B (n : ℤ)).mpr
    have ho : n % 2 = 1 := Nat.odd_iff.mp (Nat.coprime_two_right.mp hh.2.2)
    exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2.1, by omega⟩
  · intro m hm n hn he
    exact_mod_cast he
  · intro w hw
    have hh := (mem_oddRealInterval A B w).mp hw
    have hw0 : 0 ≤ w := by exact_mod_cast (hA.trans_le hh.1).le
    have he : (w.toNat : ℤ) = w := Int.toNat_of_nonneg hw0
    have her : (w.toNat : ℝ) = (w : ℝ) := by exact_mod_cast he
    refine ⟨w.toNat, ?_, he⟩
    apply mem_filter.mpr
    have hpos : 1 ≤ w.toNat := by
      have hp : (0 : ℝ) < w.toNat := by rw [her]; exact hA.trans_le hh.1
      have hn : 0 < w.toNat := by exact_mod_cast hp
      omega
    have hupper : w.toNat ≤ N := by
      exact_mod_cast (show (w.toNat : ℝ) ≤ N by rw [her]; exact hh.2.1.trans hB)
    refine ⟨mem_Icc.mpr ⟨hpos, hupper⟩, ?_, ?_, ?_⟩
    · rw [her]; exact hh.1
    · rw [her]; exact hh.2.1
    · apply Nat.coprime_two_right.mpr
      apply Nat.odd_iff.mpr
      omega
  · intro n hn
    simp

end TaoFivePrimes

