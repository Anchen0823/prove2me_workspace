param([ValidateSet('integrality','sketch')][string]$Part)
$ErrorActionPreference='Stop'
$p=$PSScriptRoot
Set-Location (Resolve-Path (Join-Path $p '../../..'))
$base='https://prove2.me/api/v1'
if(Test-Path "$p/$Part-response.json"){Get-Content "$p/$Part-response.json";exit}
if(Test-Path "$p/$Part-attempt.json"){throw 'Inspect uncertain prior submission first'}
$record=Get-Content "$p/$Part-local.json" -Raw|ConvertFrom-Json
if($record.exit_code -ne 0 -or $record.sha256 -ne (Get-FileHash $record.file).Hash){throw 'Local check mismatch'}
if($Part -eq 'integrality'){
  $job=Get-Content "$p/job-scaled_A_integral.json" -Raw|ConvertFrom-Json
  if($job.status -ne 'PUBLISHED'){throw 'Child not published'}
  $id=$job.theorem_id
}else{
  $id='66a4e48a-f260-4615-92d3-686ca9356509'
  foreach($name in @('integral_identity','scaled_integral_bounds','scaled_A_integral','fractional_lower_bound_conjecture')){
    if((Get-Content "$p/job-$name.json" -Raw|ConvertFrom-Json).status -ne 'PUBLISHED'){throw 'Missing child'}
  }
}
$code=Get-Content $record.file -Raw
if($code -match '\bsorry\b|\baxiom\b|import Theorems.Thm_EulerMascheroni_gamma_irrational\s'){throw 'Disallowed proof code'}
$c=Get-Content credentials.json -Raw|ConvertFrom-Json
$h=@{Authorization="Bearer $($c.access_token)"}
$t=Invoke-RestMethod -Uri "$base/theorems/$id" -Headers $h
if($t.mathlib_rev -ne '0df444a360eaa60ab8c11dca51a86af692955474'){throw 'Environment mismatch'}
$t|ConvertTo-Json -Depth 40|Set-Content "$p/$Part-target-before.json"
@{theorem_id=$id;sha256=$record.sha256;started_at=(Get-Date).ToString('o')}|ConvertTo-Json|Set-Content "$p/$Part-attempt.json"
$r=Invoke-RestMethod -Method Post -Uri "$base/verify" -Headers $h -Form @{
  theorem_id=$id;file=Get-Item $record.file;explanation=Get-Content "$p/$Part-explanation.md" -Raw
} -TimeoutSec 60
$r|ConvertTo-Json -Depth 20|Set-Content "$p/$Part-response.json"
$r|Select-Object submission_id,status|ConvertTo-Json
