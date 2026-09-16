import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

set_option autoImplicit false

namespace WeakGoldbach

/-- Finite segmented sieve coverage obligation for the extension range
$(4\cdot 10^{14},\,4\cdot 10^{18}]$ in blocks of one million; the
computational data remain open.  Block `b` is
$[4\cdot10^{14}+b\cdot10^6,\ 4\cdot10^{14}+(b+1)\cdot10^6-1]$ clipped to
$4\cdot10^{18}$, the small-prime bound is $9781$, and the sieve cutoff is
$2\cdot10^9$. -/
theorem verified_range_sieve_coverage (b : ℕ) (hb : b < 4000000000001) :
    ((Finset.Icc (max 4 (4 * 10 ^ 14 + b * 1000000))
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1))).filter
        (fun n => Even n)) ⊆
    GoldbachSieve.pairSums 9781 (4 * 10 ^ 14 + b * 1000000 - 9781)
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1)) 2000000000 := by
  sorry

end WeakGoldbach
