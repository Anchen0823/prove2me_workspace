import examples.«five-primes».RosserLcmCertificate

namespace TaoFivePrimes

/-- Split the LCM so successive certificates need only compute the new block. -/
theorem lcmUpto_split (a b : ℕ) (hab : a ≤ b) :
    Nat.lcmUpto b = Nat.lcm (Nat.lcmUpto a) ((Finset.Ioc a b).lcm id) := by
  have hs : Finset.Icc 1 b = Finset.Icc 1 a ∪ Finset.Ioc a b := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  simp only [Nat.lcmUpto, hs, Finset.lcm_union]
  rfl

/-- An exact previous value and a local block computation certify the next value. -/
theorem lcmUpto_eq_of_block (a b A B : ℕ) (hab : a ≤ b)
    (hprev : Nat.lcmUpto a = A)
    (hstep : Nat.lcm A ((Finset.Ioc a b).lcm id) = B) :
    Nat.lcmUpto b = B := by
  rw [lcmUpto_split a b hab, hprev]
  exact hstep

end TaoFivePrimes
