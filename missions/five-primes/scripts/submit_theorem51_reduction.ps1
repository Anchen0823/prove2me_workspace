param([ValidateSet('typeI','parent')][string]$Part)
$ErrorActionPreference='Stop'
Set-Location (Resolve-Path (Join-Path $PSScriptRoot '../../..')).Path
$base='https://prove2.me/api/v1'
$c=Get-Content credentials.json -Raw|ConvertFrom-Json
$h=@{Authorization="Bearer $($c.access_token)"}
if($Part -eq 'typeI'){
  $job=Get-Content missions/five-primes/verification/theorem51-typeI-publish-job.json -Raw|ConvertFrom-Json
  if($job.status -ne 'PUBLISHED'){throw 'Type I node not published'}
  $id=$job.theorem_id
  $name='TaoFivePrimes.theorem51_typeI_bound'
  $file='Solutions/Sol_TaoFivePrimes_theorem51_typeI_bound.lean'
  $record='missions/five-primes/verification/typeI-leaf'
  $explanation='missions/five-primes/typeI-leaf-explanation.md'
  $reference='Theorems/Thm_TaoFivePrimes_theorem51_typeI_bound.lean'
}else{
  foreach($leaf in @('vaughan','typeI','typeII')){
    $j=Get-Content "missions/five-primes/verification/theorem51-$leaf-publish-job.json" -Raw|ConvertFrom-Json
    if($j.status -ne 'PUBLISHED'){throw 'A child is not yet published'}
  }
  $id='e1794571-24bf-41f1-8f08-9296fbea9a90'
  $name='TaoFivePrimes.theorem51_unit_numerator_bound'
  $file='Solutions/Sol_TaoFivePrimes_theorem51_unit_numerator_bound_sketch.lean'
  $record='missions/five-primes/verification/theorem51-sketch'
  $explanation='missions/five-primes/theorem51-reduction-explanation.md'
  $reference='Theorems/Thm_TaoFivePrimes_theorem51_unit_numerator_bound.lean'
}
if(Test-Path "$record-submit-response.json"){Get-Content "$record-submit-response.json";exit}
if(Test-Path "$record-submit-attempt.json"){throw 'Inspect uncertain prior submission'}
$t=Invoke-RestMethod -Uri "$base/theorems/$id" -Headers $h -TimeoutSec 30
if($t.status -ne 'Open' -or $t.mathlib_rev -ne '0df444a360eaa60ab8c11dca51a86af692955474'){throw 'Target changed'}
$v=Get-Content "$record-local-result.json" -Raw|ConvertFrom-Json
if($v.exit_code -ne 0 -or $v.sha256 -ne (Get-FileHash $file).Hash){throw 'Local verification mismatch'}
if($Part -eq 'typeI' -and $v.sorryAx_found){throw 'Unproved proof dependency'}
$s=Get-Content $file -Raw
if($s -match '\bsorry\b|\baxiom\b|import examples\.') {throw 'Unexpected proof placeholder or local import'}
if($Part -eq 'typeI' -and $s -match 'import Theorems\.') {throw 'Type I must be a complete proof'}
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
