import examples.«five-primes».RosserLcmBlocks

namespace EulerMascheroni.Sondow

/-- Merge two separately checked interval certificates. -/
theorem intervalLcm_eq_of_split (a m b L R V : ℕ) (ham : a ≤ m) (hmb : m ≤ b)
    (hL : (Finset.Ioc a m).lcm id = L)
    (hR : (Finset.Ioc m b).lcm id = R)
    (hV : Nat.lcm L R = V) : (Finset.Ioc a b).lcm id = V := by
  have hs : Finset.Ioc a b = Finset.Ioc a m ∪ Finset.Ioc m b := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  rw [hs, Finset.lcm_union, hL, hR]
  exact hV

/-- Compact variant whose numeric certificate values are inferred from the proofs and target. -/
theorem intervalLcm_eq_of_split_compact (a m b : ℕ) {L R V : ℕ}
    (ham : a ≤ m) (hmb : m ≤ b)
    (hL : (Finset.Ioc a m).lcm id = L)
    (hR : (Finset.Ioc m b).lcm id = R)
    (hV : Nat.lcm L R = V) : (Finset.Ioc a b).lcm id = V :=
  intervalLcm_eq_of_split a m b L R V ham hmb hL hR hV

/-- Extend a prefix using an already checked interval value. -/
theorem lcmUpto_eq_of_certified_block (a b A R B : ℕ) (hab : a ≤ b)
    (hprev : Nat.lcmUpto a = A)
    (hblock : (Finset.Ioc a b).lcm id = R)
    (hmerge : Nat.lcm A R = B) : Nat.lcmUpto b = B := by
  apply TaoFivePrimes.lcmUpto_eq_of_block a b A B hab hprev
  simpa only [hblock] using hmerge

/-- Compact variant whose numeric certificate values are inferred from the proofs and target. -/
theorem lcmUpto_eq_of_certified_block_compact (a b : ℕ) {A R B : ℕ}
    (hab : a ≤ b)
    (hprev : Nat.lcmUpto a = A)
    (hblock : (Finset.Ioc a b).lcm id = R)
    (hmerge : Nat.lcm A R = B) : Nat.lcmUpto b = B :=
  lcmUpto_eq_of_certified_block a b A R B hab hprev hblock hmerge

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.intervalLcm_eq_of_split
#print axioms EulerMascheroni.Sondow.intervalLcm_eq_of_split_compact
#print axioms EulerMascheroni.Sondow.lcmUpto_eq_of_certified_block
#print axioms EulerMascheroni.Sondow.lcmUpto_eq_of_certified_block_compact
