import Mathlib

namespace TaoFivePrimes

/-- Monotonicity lets an upper endpoint certificate cover an entire interval. -/
theorem psi_interval_upper (a b y C : ℝ) (hC : 0 ≤ C)
    (hay : a ≤ y) (hyb : y ≤ b) (hend : Chebyshev.psi b < C * a) :
    Chebyshev.psi y < C * y :=
  lt_of_le_of_lt (Chebyshev.psi_mono hyb)
    (lt_of_lt_of_le hend (mul_le_mul_of_nonneg_left hay hC))

/-- A finite interval cover reduces the finite Rosser range to endpoint bounds. -/
theorem rosser_finite_of_interval_cover (N : ℕ) (s : Finset (ℕ × ℕ))
    (hcover : ∀ n : ℕ, 0 < n → n < N →
      ∃ ab ∈ s, ab.1 ≤ n ∧ n ≤ ab.2)
    (hcheck : ∀ ab ∈ s, Chebyshev.psi (ab.2 : ℝ) < 1.03883 * (ab.1 : ℝ)) :
    ∀ n : ℕ, 0 < n → n < N → Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by
  intro n hn hN
  obtain ⟨ab, hab, ha, hb⟩ := hcover n hn hN
  exact psi_interval_upper ab.1 ab.2 n 1.03883 (by norm_num)
    (by exact_mod_cast ha) (by exact_mod_cast hb) (hcheck ab hab)

end TaoFivePrimes
