$ErrorActionPreference='Stop'
Set-Location (Split-Path $PSScriptRoot -Parent)
$base='https://prove2.me/api/v1'
$c=Get-Content credentials.json -Raw|ConvertFrom-Json
$h=@{Authorization="Bearer $($c.access_token)"}
$id='cba0b2b8-5272-44e3-8764-6f3c559ebc64'
$p='Solutions/Sol_TaoFivePrimes_small_q_modulus_transfer_source_envelope.lean'
$record='missions/five-primes/verification/modulus-transfer'
if(Test-Path "$record-submit-response.json"){Get-Content "$record-submit-response.json";exit}
if(Test-Path "$record-submit-attempt.json"){throw 'Uncertain prior submission; inspect history.'}
$t=Invoke-RestMethod -Uri "$base/theorems/$id" -Headers $h -TimeoutSec 30
$prior=Get-Content "missions/five-primes/research/dependency-$id-current.json" -Raw|ConvertFrom-Json
if($t.status -ne 'Open' -or $t.formal_statement -ne $prior.formal_statement -or $t.mathlib_rev -ne '0df444a360eaa60ab8c11dca51a86af692955474'){throw 'Target changed'}
$check=Get-Content "$record-local-result.json" -Raw|ConvertFrom-Json
if($check.exit_code -ne 0 -or (Get-FileHash $p).Hash -ne $check.sha256){throw 'Local verification mismatch'}
$s=Get-Content $p -Raw
if($s -match '\bsorry\b|\baxiom\b|import Theorems\.') {throw 'Unexpected assumption'}
$actual=[regex]::Match($s,'(?s)theorem solution\s*(.*?)\s*:= by').Groups[1].Value -replace '\s',''
$expected=[regex]::Match($t.formal_statement,'(?s)theorem small_q_modulus_transfer_source_envelope\s*(.*?)\s*:= by').Groups[1].Value -replace '\s',''
if(-not $actual -or $actual -ne $expected){throw 'Signature mismatch'}
@{theorem_id=$id;sha256=$check.sha256;started_at=(Get-Date).ToString('o')}|ConvertTo-Json|Set-Content "$record-submit-attempt.json"
$r=Invoke-RestMethod -Method Post -Uri "$base/verify" -Headers $h -Form @{theorem_id=$id;file=Get-Item $p;explanation=Get-Content missions/five-primes/modulus-transfer-explanation.md -Raw} -TimeoutSec 60
$r|ConvertTo-Json -Depth 30|Set-Content "$record-submit-response.json"
$r|Select-Object submission_id,status|ConvertTo-Json
