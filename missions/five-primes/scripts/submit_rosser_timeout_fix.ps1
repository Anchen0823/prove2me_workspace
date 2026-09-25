$ErrorActionPreference = 'Stop'
Set-Location (Resolve-Path (Join-Path $PSScriptRoot '../../..')).Path
$base = 'https://prove2.me/api/v1'
$credentials = Get-Content credentials.json -Raw | ConvertFrom-Json
$headers = @{ Authorization = "Bearer $($credentials.access_token)" }
$prefix = 'missions/five-primes/verification/rosser-timeout-fixed'
if (Test-Path "$prefix-submit-response.json") {
    Get-Content "$prefix-submit-response.json"
    exit 0
}
if (Test-Path "$prefix-submit-attempt.json") {
    throw 'A previous attempt exists. Inspect server submissions before retrying.'
}
$targetId = 'cf6be7a8-2493-479a-9d57-6ee8535546d1'
$prior = Invoke-RestMethod "$base/verify?submission_id=603f8cd6-63dc-4609-86ab-78ad326fcf66" -Headers $headers -TimeoutSec 30
if ($prior.status -ne 'ERROR' -or $prior.error_message -ne 'Verification timed out after 300s') {
    throw 'The prior verdict differs from the diagnosed timeout.'
}
$target = Invoke-RestMethod "$base/theorems/$targetId" -Headers $headers -TimeoutSec 30
$expected = Get-Content missions/five-primes/research/rosser-timeout-target.json -Raw | ConvertFrom-Json
if ($target.status -ne 'Open' -or $target.formal_statement -ne $expected.formal_statement -or
    $target.mathlib_rev -ne $expected.mathlib_rev) { throw 'The target changed.' }
$path = 'Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_psi_bound.lean'
$check = Get-Content "$prefix-local-result.json" -Raw | ConvertFrom-Json
if ($check.exit_code -ne 0 -or (Get-FileHash $path).Hash -ne $check.sha256) {
    throw 'The exact solution file has not passed local verification.'
}
if (Select-String -Path $path -Pattern '\bsorry\b|\bnative_decide\b|^import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_psi_bound') {
    throw 'Unexpected proof content.'
}
@{ target_id=$targetId; sha256=$check.sha256; started_at=(Get-Date -Format o) } |
    ConvertTo-Json | Set-Content "$prefix-submit-attempt.json"
$response = Invoke-RestMethod -Method Post -Uri "$base/verify" -Headers $headers -Form @{
    theorem_id=$targetId
    file=Get-Item $path
    explanation=Get-Content missions/five-primes/rosser-sketch-explanation.md -Raw
} -TimeoutSec 60
$response | ConvertTo-Json -Depth 30 | Set-Content "$prefix-submit-response.json"
$response | Select-Object submission_id,status | ConvertTo-Json
