import Solutions.Sol_WeakGoldbach_verified_two_primes_4e14_to_4e18
import Theorems.Thm_WeakGoldbach_verified_two_primes_4e14_to_4e18

set_option autoImplicit false

/-- Type check: `solution` has exactly the target's type. -/
example (m : ℕ) (hlo : 4 * 10 ^ 14 < m) (hB : m ≤ 4 * 10 ^ 18) (he : Even m) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q :=
  solution m hlo hB he

set_option pp.universes false

#check @WeakGoldbach.verified_two_primes_4e14_to_4e18
#check @solution
