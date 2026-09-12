import Mathlib.NumberTheory.Chebyshev

-- Unpublished local source placeholder; not a proved theorem.
-- Tao, arXiv:1201.6656v4, proof of Lemma 4.3, citing Schoenfeld Theorem 7.
theorem TaoFivePrimes.schoenfeld_psi_error_large (y : ℝ) (hy : 10 ^ 8 ≤ y) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by sorry
