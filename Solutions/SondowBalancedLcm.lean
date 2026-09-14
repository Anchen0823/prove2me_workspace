import examples.«five-primes».RosserLcmBlocks

namespace EulerMascheroni.Sondow

/-- A bounded-depth evaluation tree for an interval LCM. -/
def balancedBlockLcm : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => (Finset.Ioc a b).lcm id
  | depth + 1, a, b =>
      if b ≤ a + 1 then (Finset.Ioc a b).lcm id
      else Nat.lcm (balancedBlockLcm depth a ((a + b) / 2))
        (balancedBlockLcm depth ((a + b) / 2) b)

theorem balancedBlockLcm_eq (depth a b : ℕ) :
    balancedBlockLcm depth a b = (Finset.Ioc a b).lcm id := by
  induction depth generalizing a b with
  | zero => rfl
  | succ depth ih =>
    rw [balancedBlockLcm]
    split_ifs with h
    · rfl
    · rw [ih, ih]
      have hs : Finset.Ioc a b = Finset.Ioc a ((a + b) / 2) ∪
          Finset.Ioc ((a + b) / 2) b := by
        ext k
        simp only [Finset.mem_union, Finset.mem_Ioc]
        omega
      rw [hs, Finset.lcm_union]
      rfl

/-- Exact certificate interface with balanced kernel evaluation. -/
theorem lcmUpto_eq_of_balanced_block (depth a b A B : ℕ) (hab : a ≤ b)
    (hprev : Nat.lcmUpto a = A)
    (hstep : Nat.lcm A (balancedBlockLcm depth a b) = B) :
    Nat.lcmUpto b = B := by
  apply TaoFivePrimes.lcmUpto_eq_of_block a b A B hab hprev
  simpa only [balancedBlockLcm_eq] using hstep

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.lcmUpto_eq_of_balanced_block
