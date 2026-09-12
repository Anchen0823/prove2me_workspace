$ErrorActionPreference = 'Stop'
Set-Location (Split-Path $PSScriptRoot -Parent)
$parts = @(
  'import Mathlib',
  'import Definitions.Def_TaoFivePrimes_ArcSplit'
)
foreach ($name in @('FourierMoments', 'CutoffEnergy', 'CutoffDifferences',
    'FiniteDifference', 'CutoffFourierDecay', 'CircleTail', 'CircleTailIntegral',
    'PrimeUniformBound', 'ComplementaryReduction')) {
  $body = Get-Content "examples/five-primes/$name.lean" -Raw
  $body = [regex]::Replace($body, '(?m)^import [^\r\n]*\r?\n', '')
  $parts += "section`n$body`nend"
}
$target = Get-Content 'missions/five-primes/research/correlation-current.json' -Raw | ConvertFrom-Json
$statement = $target.formal_statement.Replace('theorem TaoFivePrimes.eta1_complementary_correlation', 'theorem solution')
$proof = @'
by
  apply TaoFivePrimes.complementary_correlation_of_psi x (by linarith) hr_upper ε hε
  exact TaoFivePrimes.prime_mass_le_six_mul x
'@
$statement = [regex]::Replace($statement, 'by\s+sorry\s*$', $proof)
$parts += "open MeasureTheory TaoFivePrimes`nopen scoped BigOperators ComplexConjugate`n$statement"
$output = 'Solutions/Sol_TaoFivePrimes_eta1_complementary_correlation.lean'
[IO.File]::WriteAllText((Join-Path (Get-Location) $output), ($parts -join "`n`n"))
Write-Output $output
