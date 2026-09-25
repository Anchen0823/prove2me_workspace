$ErrorActionPreference='Stop'
Set-Location (Resolve-Path (Join-Path $PSScriptRoot '../../..')).Path
$paths=@(
  'examples/five-primes/Theorem51VaughanIdentity.lean',
  'examples/five-primes/Theorem51PhaseAudit.lean',
  'examples/five-primes/Theorem51TypeIIAlgebra.lean',
  'examples/five-primes/Theorem51OddHarmonic.lean',
  'examples/five-primes/Theorem51TypeITrig.lean',
  'examples/five-primes/Theorem51DiscreteSecondDifference.lean',
  'examples/five-primes/Theorem51TypeIDiscreteAssembly.lean',
  'examples/five-primes/Theorem51CutoffAmplitude.lean',
  'examples/five-primes/Theorem51OddFourierBridge.lean',
  'examples/five-primes/Theorem51AmplitudeCalculus.lean',
  'examples/five-primes/Theorem51VariationTransfer.lean',
  'examples/five-primes/Theorem51VariationControl.lean',
  'examples/five-primes/Theorem51SlopeVariation.lean',
  'examples/five-primes/Theorem51AmplitudePrimitive.lean',
  'examples/five-primes/Theorem51ConcreteDifferences.lean',
  'examples/five-primes/Theorem51TypeIActual.lean',
  'examples/five-primes/Theorem51TypeIInterface.lean',
  'examples/five-primes/Theorem51TypeIISpacing.lean',
  'examples/five-primes/Theorem51HilbertIdentity.lean',
  'examples/five-primes/Theorem51UniformHilbert.lean',
  'examples/five-primes/Theorem51SpectralBound.lean',
  'examples/five-primes/Theorem51IntegerHilbertForm.lean',
  'examples/five-primes/Theorem51KernelError.lean',
  'examples/five-primes/Theorem51CosecantError.lean',
  'examples/five-primes/Theorem51KernelConstants.lean',
  'examples/five-primes/Theorem51CosecantForm.lean',
  'examples/five-primes/Theorem51GeometricKernel.lean',
  'examples/five-primes/Theorem51FiniteLargeSieve.lean',
  'examples/five-primes/Theorem51BlockCounting.lean',
  'examples/five-primes/Theorem51BilinearBlock.lean',
  'examples/five-primes/Theorem51TypeIICounts.lean',
  'examples/five-primes/Theorem51OddBilinearPhase.lean',
  'examples/five-primes/Theorem51OddRows.lean',
  'examples/five-primes/Theorem51CoefficientEnergy.lean',
  'examples/five-primes/Theorem51ColumnPartition.lean',
  'examples/five-primes/Theorem51PaddedRectangle.lean',
  'examples/five-primes/Theorem51ScaleIntervals.lean',
  'examples/five-primes/Theorem51ScaleCoefficients.lean',
  'examples/five-primes/Theorem51ScaleBound.lean',
  'examples/five-primes/Theorem51ScaleSigned.lean',
  'examples/five-primes/Theorem51ScaleIntegrals.lean',
  'examples/five-primes/Theorem51ScaleSupport.lean',
  'examples/five-primes/Theorem51EtaScale.lean',
  'examples/five-primes/Theorem51TypeIIFinite.lean',
  'examples/five-primes/Theorem51FiniteScaleBridge.lean',
  'examples/five-primes/Theorem51NatOddReindex.lean',
  'examples/five-primes/Theorem51ScaleReindex.lean',
  'examples/five-primes/Theorem51ActualScaleKernel.lean',
  'examples/five-primes/Theorem51ScaleIntegralBridge.lean',
  'examples/five-primes/Theorem51RootIntegrals.lean',
  'examples/five-primes/Theorem51RootNormalization.lean',
  'examples/five-primes/Theorem51IntegratedMajorant.lean',
  'examples/five-primes/Theorem51TypeIIIntegration.lean'
)
$imports=[System.Collections.Generic.HashSet[string]]::new()
$bodies=@()
$hashes=@{}
foreach($p in $paths){
  $src=Get-Content $p -Raw
  if($src -match '\bsorry\b|\baxiom\b|^import Theorems\.') {throw "Unexpected proof assumption in $p"}
  foreach($line in ($src -split '\r?\n')){
    if($line -match '^import ' -and $line -notmatch '^import examples\.'){
      [void]$imports.Add($line)
    }
  }
  $bodies += "`n-- Source: $p`nsection`n" + [regex]::Replace($src,'(?m)^import .*\r?\n','') + "`nend`n"
  $hashes[$p]=(Get-FileHash $p).Hash
}
$check='examples/five-primes/Theorem51ProgressCheck.lean'
$src=($imports -join "`n")+"`n"+($bodies -join "`n")+@'

#print axioms TaoFivePrimes.vaughan_restricted_centered_identity
#print axioms TaoFivePrimes.weighted_vaughan_centered_split
#print axioms TaoFivePrimes.vaughan_half_log_correction_support
#print axioms TaoFivePrimes.source_typeI_sine_comparison_fails
#print axioms TaoFivePrimes.unit_phase_sine_lower
#print axioms TaoFivePrimes.typeII_radical_unit
#print axioms TaoFivePrimes.typeII_round_constants
#print axioms TaoFivePrimes.unit_typeI_trigonometric_sum_signed
#print axioms TaoFivePrimes.finite_fourier_second_difference_bound
#print axioms TaoFivePrimes.unit_typeI_from_discrete_variation
#print axioms TaoFivePrimes.typeIOddAmplitude_finite
#print axioms TaoFivePrimes.typeI_odd_sum_second_difference_bound
#print axioms TaoFivePrimes.log_product_derivative_hasDerivAt
#print axioms TaoFivePrimes.typeI_curvature_majorant_integral
#print axioms TaoFivePrimes.typeI_curvature_and_jump_budget
#print axioms TaoFivePrimes.typeI_middle_slope_jump
#print axioms TaoFivePrimes.second_difference_from_bounded_variation
#print axioms TaoFivePrimes.joinedSlope_variation_budget
#print axioms TaoFivePrimes.typeI_piecewise_slope_variation
#print axioms TaoFivePrimes.typeI_real_amplitude_continuous
#print axioms TaoFivePrimes.typeI_slope_integral
#print axioms TaoFivePrimes.typeI_actual_discrete_variation
#print axioms TaoFivePrimes.unit_typeI_actual_sum
#print axioms TaoFivePrimes.theorem51_typeI_bound
#print axioms TaoFivePrimes.unit_half_block_spacing
#print axioms TaoFivePrimes.integer_hilbert_eigen_bound
#print axioms TaoFivePrimes.integer_hilbert_sum_bound
#print axioms TaoFivePrimes.bounded_kernel_error
#print axioms TaoFivePrimes.abs_cosecant_sub_inv_le_one
#print axioms TaoFivePrimes.unit_cosecant_block_bound
#print axioms TaoFivePrimes.unit_cosecant_phase_difference
#print axioms TaoFivePrimes.unit_finite_large_sieve
#print axioms TaoFivePrimes.unit_finite_large_sieve_translate
#print axioms TaoFivePrimes.integer_index_card_le
#print axioms TaoFivePrimes.odd_integer_interval_card
#print axioms TaoFivePrimes.unit_bilinear_blocks
#print axioms TaoFivePrimes.typeII_counting_constant
#print axioms TaoFivePrimes.unit_odd_rectangle
#print axioms TaoFivePrimes.theorem51Centered_energy
#print axioms TaoFivePrimes.moebius_coefficient_energy
#print axioms TaoFivePrimes.integer_interval_blocks_energy
#print axioms TaoFivePrimes.integer_block_count
#print axioms TaoFivePrimes.unit_padded_odd_rectangle
#print axioms TaoFivePrimes.scale_column_block_count
#print axioms TaoFivePrimes.scale_row_energy
#print axioms TaoFivePrimes.theorem51_scale_bound_positive
#print axioms TaoFivePrimes.theorem51_scale_bound_signed
#print axioms TaoFivePrimes.integral_log_div_factorized
#print axioms TaoFivePrimes.theorem51ScaleSum_zero_below
#print axioms TaoFivePrimes.theorem51ScaleSum_zero_above
#print axioms TaoFivePrimes.eta0_pair_scale_integral
#print axioms TaoFivePrimes.scale_pair_integrable
#print axioms TaoFivePrimes.finite_eta0_scale_integral
#print axioms TaoFivePrimes.theorem51TypeII_finite
#print axioms TaoFivePrimes.theorem51TypeII_finite_scale_integral
#print axioms TaoFivePrimes.theorem51NatScaleSum_eq
#print axioms TaoFivePrimes.theorem51TypeII_le_scale_integral
#print axioms TaoFivePrimes.theorem51_scale_weight_integrable
#print axioms TaoFivePrimes.integral_log_inv_sqrt_le
#print axioms TaoFivePrimes.integral_log_inv_mul_sqrt_le
#print axioms TaoFivePrimes.typeII_radical_normalized
#print axioms TaoFivePrimes.typeII_majorant_integral_bound
#print axioms TaoFivePrimes.theorem51_typeII_of_scale_bound
'@
Set-Content $check $src -NoNewline
$timer=[Diagnostics.Stopwatch]::StartNew()
$log='missions/five-primes/verification/theorem51-progress.log'
$toolchain=(Get-Content lean-toolchain -Raw).Trim()
$toolchainDirectory=$toolchain.Replace('/','--').Replace(':','---')
$lake=Join-Path $env:USERPROFILE ".elan/toolchains/$toolchainDirectory/bin/lake.exe"
if(-not (Test-Path -LiteralPath $lake)){throw "The pinned Lake executable was not found: $lake"}
& $lake env lean '-DautoImplicit=false' $check *> $log
$code=$LASTEXITCODE
$timer.Stop()
$result=@{
  exit_code=$code;seconds=$timer.Elapsed.TotalSeconds;files=$hashes;
  check_sha256=(Get-FileHash $check).Hash;checked_at=(Get-Date).ToString('o');
  command='lake env lean -DautoImplicit=false '+$check;
  sorryAx_found=[bool](Select-String -Path $log -SimpleMatch 'sorryAx');
  scope='Auxiliary results only. The target theorem remains unproved.'
}
$result|ConvertTo-Json -Depth 8|Set-Content missions/five-primes/verification/theorem51-progress-result.json
Get-Content $log
$result|Select-Object exit_code,seconds,sorryAx_found,scope|ConvertTo-Json
if($code -ne 0 -or $result.sorryAx_found){exit 1}








