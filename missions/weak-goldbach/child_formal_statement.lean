namespace WeakGoldbach

theorem verified_range_sieve_coverage (b : ℕ) (hb : b < 4000000000001) :
    ((Finset.Icc (max 4 (4 * 10 ^ 14 + b * 1000000))
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1))).filter
        (fun n => Even n)) ⊆
    GoldbachSieve.pairSums 9781 (4 * 10 ^ 14 + b * 1000000 - 9781)
      (min (4 * 10 ^ 18) (4 * 10 ^ 14 + (b + 1) * 1000000 - 1)) 2000000000 := by
  sorry

end WeakGoldbach
