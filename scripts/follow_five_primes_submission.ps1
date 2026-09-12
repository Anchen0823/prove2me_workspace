param([int]$MaxMinutes = 10)
$ErrorActionPreference = 'Stop'
Set-Location (Split-Path $PSScriptRoot -Parent)
$base = 'https://prove2.me/api/v1'
$dir = 'missions/five-primes/verification'
$deadline = (Get-Date).AddMinutes($MaxMinutes)
$jobs = (Get-Content "$dir/children-publish-response.json" -Raw | ConvertFrom-Json).jobs
$previous = ''
while ((Get-Date) -lt $deadline) {
  $credential = Get-Content credentials.json -Raw | ConvertFrom-Json
  $headers = @{Authorization = "Bearer $($credential.access_token)"}
  $states = foreach ($job in $jobs) {
    $result = Invoke-RestMethod -Uri "$base/publish-jobs/$($job.job_id)" -Headers $headers -TimeoutSec 40
    $result | ConvertTo-Json -Depth 20 | Set-Content "$dir/publish-$($job.job_id).json"
    $result
  }
  $summary = ($states | ForEach-Object { "$($_.theorem_name): $($_.status)" }) -join '; '
  if ($summary -ne $previous) { Write-Output $summary; $previous = $summary }
  if (@($states | Where-Object { $_.status -in @('FAILED', 'ERROR') }).Count) {
    throw 'A child publication failed; inspect the saved job response before retrying.'
  }
  if (@($states | Where-Object status -ne 'PUBLISHED').Count -eq 0) {
    $responsePath = "$dir/raw-sketch-submit-response.json"
    if (!(Test-Path $responsePath)) {
      $marker = "$dir/raw-sketch-submit-attempt.json"
      if (Test-Path $marker) { throw 'A prior submission attempt has no saved response. Inspect server submissions before retrying.' }
      $proofPath = 'Solutions/Sol_TaoFivePrimes_S1_major_arc_L2_mass_corollary49_raw.lean'
      $checked = Get-Content "$dir/raw-sketch-local-result.json" -Raw | ConvertFrom-Json
      if ((Get-FileHash $proofPath).Hash -ne $checked.sha256) { throw 'Proof changed since local validation.' }
      @{started_at = (Get-Date).ToString('o'); sha256 = $checked.sha256} |
        ConvertTo-Json | Set-Content $marker
      $response = Invoke-RestMethod -Method Post -Uri "$base/verify" -Headers $headers -Form @{
        theorem_id = '3c39e958-7602-4e59-bf6a-4ac45f8fb0a2'
        file = Get-Item $proofPath
        explanation = Get-Content 'missions/five-primes/raw-sketch-explanation.md' -Raw
      } -TimeoutSec 60
      $response | ConvertTo-Json -Depth 15 | Set-Content $responsePath
      Write-Output "Submitted proof: $($response.submission_id)"
    }
    $submission = Get-Content $responsePath -Raw | ConvertFrom-Json
    $verdict = Invoke-RestMethod -Uri "$base/verify?submission_id=$($submission.submission_id)" -Headers $headers -TimeoutSec 40
    $verdict | ConvertTo-Json -Depth 25 | Set-Content "$dir/raw-sketch-verdict.json"
    Write-Output "Proof status: $($verdict.status)"
    if ($verdict.status -ne 'PENDING') { exit 0 }
  }
  Start-Sleep -Seconds 30
}
Write-Output 'Observation window ended; jobs remain active. Resume the same job and submission IDs.'
