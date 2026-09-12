$ErrorActionPreference = 'Stop'
Set-Location (Split-Path $PSScriptRoot -Parent)
$base = 'https://prove2.me/api/v1'
$c = Get-Content credentials.json -Raw | ConvertFrom-Json
$headers = @{ Authorization = "Bearer $($c.access_token)" }
$responsePath = 'missions/five-primes/verification/rosser-sketch-submit-response.json'
if (Test-Path $responsePath) { Get-Content $responsePath; exit 0 }
$publication = Get-Content missions/five-primes/verification/rosser-middle-publish-response.json -Raw | ConvertFrom-Json
if ($publication.jobs.Count -ne 1) { throw 'Expected one publication job.' }
$job = Invoke-RestMethod -Uri "$base/publish-jobs/$($publication.jobs[0].job_id)" -Headers $headers -TimeoutSec 30
$job | ConvertTo-Json -Depth 30 | Set-Content missions/five-primes/verification/rosser-middle-publish-job.json
if ($job.status -in @('PENDING', 'COMPILING')) { Write-Output "Publication $($job.status); no proof submitted."; exit 0 }
if ($job.status -ne 'PUBLISHED') { throw "Publication failed: $($job.error_message)" }
$payload = Get-Content missions/five-primes/research/rosser-middle-payload.json -Raw | ConvertFrom-Json
if ($job.formal_statement -ne $payload.problems[0].formal_statement) { throw 'Published statement mismatch.' }
$child = Invoke-RestMethod -Uri "$base/theorems/$($job.theorem_id)" -Headers $headers -TimeoutSec 30
$child | ConvertTo-Json -Depth 40 | Set-Content missions/five-primes/research/rosser-middle-published.json
if ($child.mathlib_rev -ne '0df444a360eaa60ab8c11dca51a86af692955474') { throw 'Child environment mismatch.' }
$targetId = 'cf6be7a8-2493-479a-9d57-6ee8535546d1'
$target = Invoke-RestMethod -Uri "$base/theorems/$targetId" -Headers $headers -TimeoutSec 30
$prior = Get-Content missions/five-primes/research/rosser-before-sketch.json -Raw | ConvertFrom-Json
if ($target.status -ne 'Open' -or $target.formal_statement -ne $prior.formal_statement) { throw 'Target changed.' }
$path = 'Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_psi_bound.lean'
$check = Get-Content missions/five-primes/verification/rosser-sketch-local-result.json -Raw | ConvertFrom-Json
if ($check.exit_code -ne 0 -or (Get-FileHash $path).Hash -ne $check.sha256) { throw 'Proof hash not verified.' }
if (Select-String -Path $path -Pattern '\bsorry\b|^import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_psi_bound') { throw 'Invalid proof source.' }
$attempt = 'missions/five-primes/verification/rosser-sketch-submit-attempt.json'
if (Test-Path $attempt) { throw 'Uncertain prior attempt: inspect server submissions before retrying.' }
@{target_id=$targetId;sha256=$check.sha256;started_at=(Get-Date -Format o)} |
  ConvertTo-Json | Set-Content $attempt
$r = Invoke-RestMethod -Method Post -Uri "$base/verify" -Headers $headers -Form @{
  theorem_id=$targetId; file=Get-Item $path
  explanation=Get-Content missions/five-primes/rosser-sketch-explanation.md -Raw
} -TimeoutSec 60
$r | ConvertTo-Json -Depth 30 | Set-Content $responsePath
$r | Select-Object submission_id,status | ConvertTo-Json
