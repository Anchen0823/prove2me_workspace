$ErrorActionPreference = 'Stop'
Set-Location (Resolve-Path (Join-Path $PSScriptRoot '../../..')).Path
$parts = @('import Mathlib',
  'import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_large',
  'import Theorems.Thm_TaoFivePrimes_rosser_psi_finite_middle')
foreach ($name in @('RosserLcmCertificate', 'RosserLcmBlocks',
    'RosserCriticalEndpoint', 'RosserFinite1000Compact',
    'RosserLargeReduction', 'RosserSumBridge')) {
  $body = Get-Content "examples/five-primes/$name.lean" -Raw
  $body = [regex]::Replace($body, '(?m)^import [^\r\n]*\r?\n', '')
  if ($name -eq 'RosserLcmCertificate') {
    # These standalone demonstrations are not used by the final proof.
    $body = [regex]::Replace($body,
      'set_option maxRecDepth 16384 in\r?\nset_option maxHeartbeats 1000000 in\r?\ntheorem lcm_1000_upper[\s\S]*?(?=/-- A power certificate)', '')
  }
  $parts += "section`n$body`nend"
}
$parts += @'
open scoped BigOperators ArithmeticFunction.vonMangoldt

theorem solution :
    ∀ x : ℕ, 0 < x →
      (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ)) <
        1.03883 * (x : ℝ) := by
  intro x hx
  rw [← TaoFivePrimes.psi_nat_eq_sum_range]
  apply TaoFivePrimes.rosser_of_finite_and_error ?_
    TaoFivePrimes.schoenfeld_psi_error_large x hx
  intro n hn hN
  by_cases hs : n ≤ 1000
  · exact TaoFivePrimes.rosser_up_to_1000 n hn hs
  · exact TaoFivePrimes.rosser_psi_finite_middle n (by omega) hN
'@
$output = 'Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_psi_bound.lean'
[IO.File]::WriteAllText((Join-Path (Get-Location) $output), ($parts -join "`n`n"))
python missions/five-primes/scripts/optimize_rosser_timeout.py
if ($LASTEXITCODE -ne 0) { throw 'Rosser case-tree generation failed.' }
Write-Output $output
