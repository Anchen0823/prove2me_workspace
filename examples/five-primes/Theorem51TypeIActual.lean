import examples.«five-primes».Theorem51ConcreteDifferences
import examples.«five-primes».Theorem51TypeIDiscreteAssembly
import examples.«five-primes».Theorem51OddFourierBridge

namespace TaoFivePrimes

/-- Full Type I analytic estimate for the literal odd-lattice amplitudes.
There is no Fourier-decay, smoothness, or variation hypothesis left. -/
theorem unit_typeI_actual_sum
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ)
    (hx : 1 ≤ x) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUVq : U * V < (q : ℝ) - 1) (ha : a.natAbs = 1)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ U * V ∧ d.Coprime 2)
    (hc : ∀ d ∈ s, ‖c d‖ ≤ 1)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ d ∈ s, ‖∑' n : ℤ, typeIOddAmplitude x d (c d) n *
      expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ))‖) ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
        Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  simp_rw [norm_odd_fourier_eq_geometric]
  apply unit_typeI_from_discrete_variation x alpha beta U V a q s
    (fun d => typeIOddAmplitude x d (c d)) hx hU hV hUVq ha hs hphase hbeta
  · intro d hd
    exact typeIOddAmplitude_finite x d (c d) (by linarith) (by exact_mod_cast (hs d hd).1)
  · intro d hd
    apply typeI_actual_discrete_variation x d (c d)
    · exact_mod_cast (hs d hd).1
    · have hdUV := (hs d hd).2.1
      linarith
    · exact hc d hd

end TaoFivePrimes
