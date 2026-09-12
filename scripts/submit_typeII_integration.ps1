$ErrorActionPreference='Stop'
Set-Location (Split-Path $PSScriptRoot -Parent)
$base='https://prove2.me/api/v1'
$c=Get-Content credentials.json -Raw|ConvertFrom-Json
$h=@{Authorization="Bearer $($c.access_token)"}
$Part='scale'
$id='b46d7b94-7c1d-4d9d-980f-18230c005f4c'
$name='TaoFivePrimes.theorem51_typeII_of_scale_bound'
$file='Solutions/Sol_TaoFivePrimes_theorem51_typeII_of_scale_bound.lean'
$record='missions/five-primes/verification/typeII-integration'
$explanation='missions/five-primes/typeII-integration-explanation.md'
$reference='Theorems/Thm_TaoFivePrimes_theorem51_typeII_of_scale_bound.lean'
if(Test-Path "$record-submit-response.json"){Get-Content "$record-submit-response.json";exit}
if(Test-Path "$record-submit-attempt.json"){throw 'Inspect uncertain prior submission'}
$t=Invoke-RestMethod -Uri "$base/theorems/$id" -Headers $h -TimeoutSec 30
if($t.status -ne 'Open' -or $t.mathlib_rev -ne '0df444a360eaa60ab8c11dca51a86af692955474'){throw 'Target changed'}
$v=Get-Content "$record-local-result.json" -Raw|ConvertFrom-Json
if($v.exit_code -ne 0 -or $v.sha256 -ne (Get-FileHash $file).Hash){throw 'Local verification mismatch'}
if($Part -eq 'scale' -and $v.sorryAx_found){throw 'Unproved proof dependency'}
$s=Get-Content $file -Raw
if($s -match '\bsorry\b|\baxiom\b|import examples\.') {throw 'Unexpected proof placeholder or local import'}
if($Part -eq 'scale' -and $s -match 'import Theorems\.') {throw 'Integration must be a complete proof'}
$actual=[regex]::Match($s,'(?s)theorem solution\s*(.*?)\s*:= by').Groups[1].Value -replace '\s',''
$pattern='(?s)theorem '+[regex]::Escape($name)+'\s*(.*?)\s*:= by'
$expected=[regex]::Match($t.formal_statement,$pattern).Groups[1].Value -replace '\s',''
$localExpected=[regex]::Match((Get-Content $reference -Raw),$pattern).Groups[1].Value -replace '\s',''
if(-not $actual -or $actual -ne $expected -or $expected -ne $localExpected){throw 'Signature changed'}
@{theorem_id=$id;sha256=$v.sha256;started_at=(Get-Date).ToString('o')}|ConvertTo-Json|Set-Content "$record-submit-attempt.json"
$r=Invoke-RestMethod -Method Post -Uri "$base/verify" -Headers $h -Form @{
  theorem_id=$id;file=Get-Item $file;explanation=Get-Content $explanation -Raw
} -TimeoutSec 60
$r|ConvertTo-Json -Depth 20|Set-Content "$record-submit-response.json"
$r|Select-Object submission_id,status|ConvertTo-Json


