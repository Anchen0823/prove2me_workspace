$ErrorActionPreference = 'Stop'
Set-Location (Resolve-Path (Join-Path $PSScriptRoot '../../..')).Path
$base = 'https://prove2.me/api/v1'
$c = Get-Content credentials.json -Raw | ConvertFrom-Json
$headers = @{Authorization="Bearer $($c.access_token)"}
$responsePath = 'missions/five-primes/verification/large-q-submit-response.json'
if (Test-Path $responsePath) { Get-Content $responsePath; exit 0 }
$job = Invoke-RestMethod -Uri "$base/publish-jobs/9bfbdc53-11a5-4feb-a954-dbe91cfe41c5" -Headers $headers -TimeoutSec 30
$job | ConvertTo-Json -Depth 40 | Set-Content missions/five-primes/verification/large-q-publish-job.json
if ($job.status -in @('PENDING','COMPILING')) { Write-Output "Source publication $($job.status); proof not submitted."; exit 0 }
if ($job.status -ne 'PUBLISHED') { throw "Publication failed: $($job.error_message)" }
$payload = Get-Content missions/five-primes/research/large-q-source-payload.json -Raw | ConvertFrom-Json
if ($job.formal_statement -ne $payload.problems[0].formal_statement) { throw 'Published statement differs from the reviewed source.' }
$child = Invoke-RestMethod -Uri "$base/theorems/$($job.theorem_id)" -Headers $headers -TimeoutSec 30
$child | ConvertTo-Json -Depth 40 | Set-Content missions/five-primes/research/large-q-source-published.json
if ($child.mathlib_rev -ne '0df444a360eaa60ab8c11dca51a86af692955474') { throw 'Source environment mismatch.' }
$targetId = '3d23bf2a-4938-4e21-a27c-2733e36173b1'
$target = Invoke-RestMethod -Uri "$base/theorems/$targetId" -Headers $headers -TimeoutSec 30
$prior = Get-Content missions/five-primes/research/large-q-target.json -Raw | ConvertFrom-Json
if ($target.status -ne 'Open' -or $target.formal_statement -ne $prior.formal_statement -or $target.mathlib_rev -ne $prior.mathlib_rev) { throw 'Target changed.' }
$path = 'Solutions/Sol_TaoFivePrimes_exp_sum_estimate_large_q_unit_source_envelope.lean'
$check = Get-Content missions/five-primes/verification/large-q-local-result.json -Raw | ConvertFrom-Json
if ($check.exit_code -ne 0 -or (Get-FileHash $path).Hash -ne $check.sha256) { throw 'Unverified solution hash.' }
if (Select-String -Path $path -Pattern '\bsorry\b|^import Theorems.Thm_TaoFivePrimes_exp_sum_estimate_large_q_unit_source_envelope') { throw 'Invalid source content.' }
$attempt = 'missions/five-primes/verification/large-q-submit-attempt.json'
if (Test-Path $attempt) { throw 'Uncertain previous attempt: inspect submission history before retrying.' }
@{target_id=$targetId;sha256=$check.sha256;started_at=(Get-Date).ToString('o')} |
  ConvertTo-Json | Set-Content $attempt
$r = Invoke-RestMethod -Method Post -Uri "$base/verify" -Headers $headers -Form @{
  theorem_id=$targetId; file=Get-Item $path
  explanation=Get-Content missions/five-primes/large-q-sketch-explanation.md -Raw
} -TimeoutSec 60
$r | ConvertTo-Json -Depth 30 | Set-Content $responsePath
$r | Select-Object submission_id,status | ConvertTo-Json
