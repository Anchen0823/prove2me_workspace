import Mathlib

set_option autoImplicit false

namespace WeakGoldbach

theorem verified_two_primes_4e14_to_4e18 (m : ℕ) (hlo : 4 * 10 ^ 14 < m)
    (hB : m ≤ 4 * 10 ^ 18) (he : Even m) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by
  sorry

end WeakGoldbach
