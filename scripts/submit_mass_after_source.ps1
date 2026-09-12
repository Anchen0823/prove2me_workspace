$ErrorActionPreference = 'Stop'
Set-Location (Split-Path $PSScriptRoot -Parent)
$base = 'https://prove2.me/api/v1'
$cred = Get-Content credentials.json -Raw | ConvertFrom-Json
$headers = @{ Authorization = "Bearer $($cred.access_token)" }
$responsePath = 'missions/five-primes/verification/mass-sketch-submit-response.json'
if (Test-Path $responsePath) {
  Get-Content $responsePath
  exit 0
}
$job = Invoke-RestMethod -Uri "$base/publish-jobs/9d1e49ba-ffcf-4edd-9ef6-967edcfc42fc" -Headers $headers -TimeoutSec 30
$job | ConvertTo-Json -Depth 30 | Set-Content missions/five-primes/verification/chebyshev-source-job.json
if ($job.status -eq 'PENDING') { Write-Output 'Source publication PENDING; no proof submitted.'; exit 0 }
if ($job.status -ne 'PUBLISHED') { throw "Publication status: $($job.status); $($job.error_message)" }
$payload = Get-Content missions/five-primes/research/chebyshev-source-payload.json -Raw | ConvertFrom-Json
if ($job.formal_statement -ne $payload.problems[0].formal_statement) { throw 'Published statement differs from the reviewed payload.' }
$source = Invoke-RestMethod -Uri "$base/theorems/$($job.theorem_id)" -Headers $headers -TimeoutSec 30
$source | ConvertTo-Json -Depth 40 | Set-Content missions/five-primes/research/chebyshev-source-published.json
if ($source.mathlib_rev -ne '0df444a360eaa60ab8c11dca51a86af692955474') { throw 'Source environment mismatch.' }
$targetId = 'f4cd87ed-a92c-4886-b0b7-e81a95dd0134'
$target = Invoke-RestMethod -Uri "$base/theorems/$targetId" -Headers $headers -TimeoutSec 30
$prior = Get-Content missions/five-primes/research/mass-before-sketch.json -Raw | ConvertFrom-Json
if ($target.formal_statement -ne $prior.formal_statement) { throw 'Target statement changed.' }
if ($target.status -ne 'Open') { throw "Target status changed: $($target.status)" }
$path = 'Solutions/Sol_TaoFivePrimes_eta1_quadratic_prime_mass.lean'
$check = Get-Content missions/five-primes/verification/mass-sketch-local-result.json -Raw | ConvertFrom-Json
if ($check.exit_code -ne 0 -or (Get-FileHash $path).Hash -ne $check.sha256) { throw 'Source hash does not match local validation.' }
if (Select-String -Path $path -Pattern '\bsorry\b|^import Theorems.Thm_TaoFivePrimes_eta1_quadratic_prime_mass') { throw 'Unexpected sorry or target import.' }
$attempt = 'missions/five-primes/verification/mass-sketch-submit-attempt.json'
if (Test-Path $attempt) { throw 'Prior submission attempt without response; inspect server history before retrying.' }
@{ target_id = $targetId; sha256 = $check.sha256; started_at = (Get-Date -Format o) } | ConvertTo-Json | Set-Content $attempt
$response = Invoke-RestMethod -Method Post -Uri "$base/verify" -Headers $headers -Form @{
  theorem_id = $targetId
  file = Get-Item $path
  explanation = Get-Content missions/five-primes/mass-sketch-explanation.md -Raw
} -TimeoutSec 60
$response | ConvertTo-Json -Depth 30 | Set-Content $responsePath
$response | Select-Object submission_id, status | ConvertTo-Json
