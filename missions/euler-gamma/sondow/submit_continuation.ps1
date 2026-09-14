param([ValidateSet('integral_bounds','remainder_tendsto_zero','cutoffError_tendsto_zero','scaled_integral_bounds','integral_identity','finite_cutoff_identity')][string]$Name)
$ErrorActionPreference='Stop'
Set-Location (Resolve-Path (Join-Path $PSScriptRoot '../../..'))
$p=Join-Path $PSScriptRoot 'continuation'
$base='https://prove2.me/api/v1'
if(Test-Path "$p/$Name-response.json"){Get-Content "$p/$Name-response.json";exit}
if(Test-Path "$p/$Name-attempt.json"){throw 'Inspect uncertain prior submission'}
$v=Get-Content "$p/$Name-local.json" -Raw|ConvertFrom-Json
if($v.exit_code -ne 0 -or $v.sha256 -ne (Get-FileHash $v.file).Hash){throw 'Verification hash mismatch'}
if($Name -eq 'scaled_integral_bounds'){$id='00b4cd42-5f36-4d22-ab0f-2a87c9194496'}
elseif($Name -eq 'integral_identity'){$id='747d96a7-9576-41e1-801a-228e9d36c4cd'}
elseif($Name -eq 'finite_cutoff_identity'){$id='d27e4fda-75c8-48f4-bc64-5050678b070c'}
else{$j=Get-Content "$p/job-$Name.json" -Raw|ConvertFrom-Json; if($j.status -ne 'PUBLISHED'){throw 'Not published'}; $id=$j.theorem_id}
$code=Get-Content $v.file -Raw
if($code -match '\bsorry\b|\baxiom\b'){throw 'Proof placeholder'}
if($code -match ('import Theorems.Thm_EulerMascheroni_Sondow_'+$Name+'\s')){throw 'Self import'}
if($Name -in @('integral_bounds','remainder_tendsto_zero','cutoffError_tendsto_zero','finite_cutoff_identity') -and
  ((Get-Content "$p/$Name-local.log" -Raw) -match 'sorryAx')){throw 'Unproved dependency in direct proof'}
$c=Get-Content credentials.json -Raw|ConvertFrom-Json
$h=@{Authorization="Bearer $($c.access_token)"}
$t=Invoke-RestMethod -Uri "$base/theorems/$id" -Headers $h
if($t.mathlib_rev -ne '0df444a360eaa60ab8c11dca51a86af692955474'){throw 'Environment mismatch'}
$expected=(Get-Content "Theorems/Thm_EulerMascheroni_Sondow_$Name.lean" -Raw) -split 'theorem EulerMascheroni.Sondow.'+$Name,2
$sig=($expected[1] -replace ':= by sorry\s*$','') -replace '\s',''
$remote=($t.formal_statement -split 'theorem EulerMascheroni.Sondow.'+$Name,2)[1] -replace ':= by sorry\s*$','' -replace '\s',''
if($sig -ne $remote){throw 'Target statement changed'}
$t|ConvertTo-Json -Depth 60|Set-Content "$p/$Name-target-before.json"
@{theorem_id=$id;sha256=$v.sha256;started_at=(Get-Date).ToString('o')}|ConvertTo-Json|Set-Content "$p/$Name-attempt.json"
$r=Invoke-RestMethod -Method Post -Uri "$base/verify" -Headers $h -Form @{
  theorem_id=$id;file=Get-Item $v.file;
  explanation=Get-Content (Join-Path $PSScriptRoot "continuation_${Name}_explanation.md") -Raw
} -TimeoutSec 60
$r|ConvertTo-Json -Depth 30|Set-Content "$p/$Name-response.json"
$r|Select-Object submission_id,status|ConvertTo-Json
