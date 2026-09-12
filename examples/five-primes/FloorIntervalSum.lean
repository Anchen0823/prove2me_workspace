import Mathlib

open scoped BigOperators

namespace TaoFivePrimes

theorem mem_floor_Ioc_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ ↔ a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  rw [Finset.mem_Ioc, Nat.floor_lt ha, Nat.le_floor_iff hb]

theorem sum_range_indicator_Ioc (N a b : ℕ) (hb : b ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), if n ∈ Finset.Ioc a b then f n else 0) =
      ∑ n ∈ Finset.Ioc a b, f n := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  · intro n _
    rfl

end TaoFivePrimes
