$ErrorActionPreference = 'Stop'
Set-Location (Split-Path $PSScriptRoot -Parent)
$responsePath = 'missions/five-primes/verification/rosser-middle-publish-response.json'
if (Test-Path $responsePath) { Get-Content $responsePath; exit 0 }
$check = Get-Content missions/five-primes/verification/rosser-sketch-local-result.json -Raw | ConvertFrom-Json
$solution = 'Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_psi_bound.lean'
if ($check.exit_code -ne 0 -or (Get-FileHash $solution).Hash -ne $check.sha256) {
  throw 'The exact sketch has not passed local verification at its current hash.'
}
$c = Get-Content credentials.json -Raw | ConvertFrom-Json
$headers = @{ Authorization = "Bearer $($c.access_token)" }
$base = 'https://prove2.me/api/v1'
$target = Invoke-RestMethod -Uri "$base/theorems/cf6be7a8-2493-479a-9d57-6ee8535546d1" -Headers $headers -TimeoutSec 30
$prior = Get-Content missions/five-primes/research/rosser-before-sketch.json -Raw | ConvertFrom-Json
if ($target.status -ne 'Open' -or $target.formal_statement -ne $prior.formal_statement -or
    $target.mathlib_rev -ne '0df444a360eaa60ab8c11dca51a86af692955474') { throw 'Target changed.' }
$attempt = 'missions/five-primes/verification/rosser-middle-publish-attempt.json'
if (Test-Path $attempt) { throw 'An uncertain previous attempt requires server history inspection.' }
$payloadPath = 'missions/five-primes/research/rosser-middle-payload.json'
@{started_at=(Get-Date -Format o); payload_sha256=(Get-FileHash $payloadPath).Hash} |
  ConvertTo-Json | Set-Content $attempt
$r = Invoke-RestMethod -Method Post -Uri "$base/submit-problem" -Headers $headers -ContentType 'application/json' -Body (Get-Content $payloadPath -Raw) -TimeoutSec 60
$r | ConvertTo-Json -Depth 30 | Set-Content $responsePath
$r | ConvertTo-Json -Depth 10
