-- Public-mission submission for EqualTwoSquares.explicit_family_chain.

import Mathlib

theorem solution {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ) < 2 * n - 1 ∧
      2 * n - 1 < n^2 - n - 1 ∧
        n^2 - n - 1 < n^2 - n + 1 := by
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith
