$ErrorActionPreference = 'Stop'
Set-Location (Split-Path $PSScriptRoot -Parent)
$parts = @('import Mathlib', 'import Definitions.Def_TaoFivePrimes_ArcSplit',
  'import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_large')
foreach ($name in @('CutoffEnergy', 'SieveLoss', 'SieveLossNumeric', 'CutoffSieveLoss',
    'PrimeMassReduction', 'QuadraticAbel', 'TrapezoidAbel', 'CutoffPartition',
    'FloorIntervalSum', 'CutoffSumPartition', 'AbelMainTerm', 'AbelKernelMass',
    'AbelErrorBound', 'AbelErrorAssembly', 'QuadraticMassFromChebyshev')) {
  $body = Get-Content "examples/five-primes/$name.lean" -Raw
  $body = [regex]::Replace($body, '(?m)^import [^\r\n]*\r?\n', '')
  $parts += "section`n$body`nend"
}
$target = Get-Content 'missions/five-primes/research/mass-before-sketch.json' -Raw | ConvertFrom-Json
$statement = $target.formal_statement.Replace('theorem TaoFivePrimes.eta1_quadratic_prime_mass', 'theorem solution')
$proof = @'
by
  apply TaoFivePrimes.quadratic_mass_of_chebyshev_error x (by linarith)
  · have he : (x : ℝ) / 10 = (1 / 10 : ℝ) * x := by ring
    rw [he]
    linarith
  · exact TaoFivePrimes.schoenfeld_psi_error_large
'@
$statement = [regex]::Replace($statement, 'by\s+sorry\s*$', $proof)
$parts += "open scoped BigOperators`nopen TaoFivePrimes`n$statement"
$output = 'Solutions/Sol_TaoFivePrimes_eta1_quadratic_prime_mass.lean'
[IO.File]::WriteAllText((Join-Path (Get-Location) $output), ($parts -join "`n`n"))
Write-Output $output
