# Check the accepted Bunkbed submission and its exact target type.
param([switch]$CheckScratch)

$ErrorActionPreference = 'Stop'
$workspace = (Resolve-Path (Join-Path $PSScriptRoot '../../..')).Path
Push-Location $workspace
try {
    $toolchain = (Get-Content lean-toolchain -Raw).Trim()
    $toolchainDirectory = $toolchain.Replace('/', '--').Replace(':', '---')
    $lake = Join-Path $env:USERPROFILE ".elan/toolchains/$toolchainDirectory/bin/lake.exe"
    if (-not (Test-Path -LiteralPath $lake)) {
        throw "The pinned Lake executable was not found: $lake"
    }
    $outputDirectory = '.lake/build/lib/lean/Solutions'
    New-Item -ItemType Directory -Force $outputDirectory | Out-Null
    $timer = [Diagnostics.Stopwatch]::StartNew()
    if ($CheckScratch) {
        $scratchOutput = '.lake/build/lib/lean/examples/bunkbed'
        New-Item -ItemType Directory -Force $scratchOutput | Out-Null
        foreach ($module in @('GroupingCore', 'GroupingAlgebra')) {
            & $lake env lean '-DautoImplicit=false' -o "$scratchOutput/$module.olean" "examples/bunkbed/$module.lean"
            if ($LASTEXITCODE -ne 0) { throw "The archived scratch module $module did not compile." }
        }
        & $lake env lean '-DautoImplicit=false' examples/bunkbed/GroupingFinal.lean
        if ($LASTEXITCODE -ne 0) { throw 'The archived final connection did not compile.' }
    }
    & $lake env lean '-DautoImplicit=false' -o "$outputDirectory/Sol_BunkbedFalse_sub_probability_grouping.olean" Solutions/Sol_BunkbedFalse_sub_probability_grouping.lean
    if ($LASTEXITCODE -ne 0) { throw 'The grouping submission did not compile.' }
    & $lake env lean '-DautoImplicit=false' examples/bunkbed/GroupingTypecheck.lean
    if ($LASTEXITCODE -ne 0) { throw 'The target-type comparison did not compile.' }
    $timer.Stop()
    Write-Output ('Grouping proof and target-type checks passed in {0:N2} seconds.' -f $timer.Elapsed.TotalSeconds)
    Write-Output 'Local platform theorem mirrors contain sorry placeholders; server verification is authoritative for their dependency status.'
}
finally {
    Pop-Location
}
