$ErrorActionPreference='Stop'
Set-Location (Resolve-Path (Join-Path $PSScriptRoot '../../..')).Path
$record='missions/five-primes/verification/integer-hilbert'
$file='Solutions/Sol_TaoFivePrimes_integer_hilbert_sum_bound.lean'
$base='https://prove2.me/api/v1'
$c=Get-Content credentials.json -Raw|ConvertFrom-Json
$headers=@{Authorization="Bearer $($c.access_token)"}
$job=Get-Content "$record-publish-job.json" -Raw|ConvertFrom-Json
if($job.status -ne 'PUBLISHED'){throw 'Wait for the existing publication job'}
if(Test-Path "$record-submit-response.json"){Get-Content "$record-submit-response.json";exit}
if(Test-Path "$record-submit-attempt.json"){throw 'Inspect uncertain prior attempt before retrying'}
$target=Invoke-RestMethod -Uri "$base/theorems/$($job.theorem_id)" -Headers $headers -TimeoutSec 30
$payload=Get-Content missions/five-primes/research/integer-hilbert-payload.json -Raw|ConvertFrom-Json
if($target.formal_statement -ne $payload.problems[0].formal_statement -or
   $target.mathlib_rev -ne $payload.env -or $target.status -ne 'Open'){throw 'Target changed'}
$v=Get-Content "$record-local-result.json" -Raw|ConvertFrom-Json
if($v.exit_code -ne 0 -or $v.sorryAx_found -or $v.sha256 -ne (Get-FileHash $file).Hash){throw 'Local verification mismatch'}
$src=Get-Content $file -Raw
if($src -match '\bsorry\b|\baxiom\b|import Theorems\.|import examples\.') {throw 'Unexpected proof dependency'}
$actual=[regex]::Match($src,'(?s)theorem solution\s*(.*?)\s*:= by').Groups[1].Value -replace '\s',''
$expected=[regex]::Match($target.formal_statement,'(?s)theorem TaoFivePrimes.integer_hilbert_sum_bound\s*(.*?)\s*:= by').Groups[1].Value -replace '\s',''
if(-not $actual -or $actual -ne $expected){throw 'Signature mismatch'}
@{theorem_id=$job.theorem_id;sha256=$v.sha256;started_at=(Get-Date).ToString('o')}|ConvertTo-Json|Set-Content "$record-submit-attempt.json"
$r=Invoke-RestMethod -Method Post -Uri "$base/verify" -Headers $headers -Form @{
 theorem_id=$job.theorem_id;file=Get-Item $file;
 explanation=Get-Content missions/five-primes/integer-hilbert-explanation.md -Raw
} -TimeoutSec 60
$r|ConvertTo-Json -Depth 20|Set-Content "$record-submit-response.json"
$r|Select-Object submission_id,status|ConvertTo-Json
