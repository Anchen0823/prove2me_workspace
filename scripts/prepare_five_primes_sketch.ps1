$ErrorActionPreference = 'Stop'
Set-Location (Split-Path $PSScriptRoot -Parent)
$parts = @(
  'import Mathlib',
  'import Definitions.Def_TaoFivePrimes_ArcSplit',
  'import Theorems.Thm_TaoFivePrimes_eta1_quadratic_prime_mass',
  'import Theorems.Thm_TaoFivePrimes_eta1_complementary_correlation'
)
foreach ($name in @('FourierMoments', 'LocalL2', 'CutoffEnergy', 'MajorArcReduction')) {
  $body = Get-Content "examples/five-primes/$name.lean" -Raw
  $parts += [regex]::Replace($body, '(?m)^import [^\r\n]*\r?\n', '')
}
$target = Get-Content 'missions/five-primes/research/target-current.json' -Raw | ConvertFrom-Json
$statement = $target.formal_statement.Replace('theorem TaoFivePrimes.S1_major_arc_L2_mass_corollary49_raw', 'theorem solution')
$proof = @'
by
  obtain ⟨ε, hε, hmass⟩ := TaoFivePrimes.eta1_quadratic_prime_mass x hc8 hneat halamo h10q
  refine ⟨ε, hε, ?_⟩
  apply TaoFivePrimes.S1_raw_of_mass_and_tail x (by linarith) ε hε hmass
  exact TaoFivePrimes.eta1_complementary_correlation x hr_lower hr_upper hc8 hneat
    halamo h10q hr0b ε hε hmass
'@
$statement = [regex]::Replace($statement, 'by\s+sorry\s*$', $proof)
$parts += "open MeasureTheory TaoFivePrimes`n$statement"
$output = 'Solutions/Sol_TaoFivePrimes_S1_major_arc_L2_mass_corollary49_raw.lean'
[IO.File]::WriteAllText((Join-Path (Get-Location) $output), ($parts -join "`n`n"))
Write-Output $output
