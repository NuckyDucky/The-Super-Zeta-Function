#Requires -Version 7.4
param(
    [Parameter(Mandatory)] [string] $AxiomCheckout,
    [Parameter(Mandatory)] [string] $LeanBin,
    [ValidateRange(1, 8)] [int] $BuildThreads = 2,
    [switch] $SampledContours
)

$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [Text.Encoding]::UTF8
$root = (Resolve-Path -LiteralPath $AxiomCheckout).Path
$bin = (Resolve-Path -LiteralPath $LeanBin).Path
$fieldSourceRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '../../../lean-ideal73')).Path
$suffix = if ($IsWindows) { '.exe' } else { '' }
$lean = Join-Path $bin ('lean' + $suffix)
$lake = Join-Path $bin ('lake' + $suffix)
$head = (& git -C $root rev-parse HEAD).Trim()
$mathlib = (& git -C (Join-Path $root '.lake/packages/mathlib') rev-parse HEAD).Trim()
$version = & $lean --version
if ($head -ne '09afbb4ce6570c1615d58509dc197fc9f0956b7d' -or
    $mathlib -ne '0493595ecd5da8ef14742febab99728f98e948e8' -or
    $version -notmatch '470d5ce1400764999581fd26d5d72b00d990b0f4') {
    throw 'Use the pinned AxiomMath sources, Mathlib, and Lean 4.35.0-rc3.'
}
$version
"AxiomMath $head"
"Mathlib $mathlib"

$inputs = [ordered]@{
    FieldTarget = '2d736feec6079b6aa96df2bfa9ab20eac0f5c859'
    DedekindDottieSetup = 'f3f1929adb407339f0473a322ffb208b94f33053'
    DedekindFieldInputs = 'cccd630c12934edafa2943819adbaf35fd52b9e6'
    DedekindFieldUniverses = 'fb339e0849ee4e882211f731e04a2b51599efe86'
}
$replayName = if ($SampledContours) { 'super-zeta-sampled-contours' } else { 'super-zeta-mixed-theta' }
$stage = (New-Item -ItemType Directory -Force -Path "$root/.lake/$replayName/src").FullName
$out = (New-Item -ItemType Directory -Force -Path "$root/.lake/$replayName/lib").FullName
if ($SampledContours) {
    $inputs.Add('DottieDyadicGeometry', '92d55ff728fdfcf2dcae06dcf33e85fb81638da4')
    $inputs.Add('DedekindFiniteDottieCover', '3925b92783ca6750d284814e844ba07182214175')
    $inputs.Add('DedekindCofinalSignedRings', '26aad230939523504635bc7f1e02299e71608a37')
}
foreach ($name in $inputs.Keys) {
    $file = Join-Path $fieldSourceRoot "$name.lean"
    $hash = (& git hash-object --no-filters -- $file).Trim()
    if ($LASTEXITCODE -ne 0 -or $hash -ne $inputs[$name]) {
        throw "$name.lean differs from the audited source. Check out with Git's automatic line-ending conversion disabled."
    }
    Copy-Item -LiteralPath $file -Destination (Join-Path $stage "$name.lean")
    "Super Zeta source $name $hash"
}
$modules = @('DedekindMixedTheta', 'DedekindMixedThetaTail')
if ($SampledContours) {
    $modules += @(
        'DedekindMixedThetaSignedRings',
        'DottieRationalContour',
        'DedekindMixedThetaCompletedRings',
        'DedekindMixedThetaOscillation',
        'DedekindMixedThetaFiniteSamples',
        'DedekindMixedThetaSampleCover',
        'DedekindMixedThetaSampleCompleteness',
        'DedekindMixedThetaPoleDominance',
        'DedekindMixedThetaClassMass',
        'DedekindMixedThetaRegularPartBound',
        'DedekindRationalCalibration',
        'DedekindRationalDottieBand',
        'DottieContourPhase',
        'DottieCayleyWeightedRiemann',
        'DottieCayleySameInput'
    )
}
foreach ($name in $modules) {
    $file = Join-Path $PSScriptRoot "$name.lean"
    $hash = (& git hash-object --no-filters -- $file).Trim()
    if ($LASTEXITCODE -ne 0) { throw "Could not hash $name.lean." }
    Copy-Item -LiteralPath $file -Destination (Join-Path $stage "$name.lean")
    "Super Zeta source $name $hash"
}

$savedPath = $env:Path
$savedLeanPath = $env:LEAN_PATH
$savedThreads = $env:LEAN_NUM_THREADS
$env:Path = $bin + [IO.Path]::PathSeparator + $env:Path

Push-Location -LiteralPath $root
try {
    $env:LEAN_NUM_THREADS = [string] $BuildThreads
    $targets = @(
        '+DedekindZetaZeroFree.LFunctions.Dedekind.HolomorphicContinuation:olean',
        '+DedekindZetaZeroFree.HarmonicAnalysis.Mellin.WeakPairPoleClearing:olean',
        '+DedekindZetaZeroFree.HarmonicAnalysis.Mellin.TailRemainder:olean',
        '+DedekindZetaZeroFree.Theta.Inversion.MixedPairGlobalSelfDuality:olean'
    )
    & $lake build @targets
    $status = $LASTEXITCODE
    "AxiomMath mixed theta imports exit=$status"
    if ($status -ne 0) { exit $status }

    $runtime = (Get-Command pwsh).Source
    $imports = & $lake env $runtime -NoLogo -NoProfile -NonInteractive -Command '$env:LEAN_PATH'
    if ($LASTEXITCODE -ne 0 -or !$imports) { throw 'Could not determine the pinned Lake import path.' }
    $env:LEAN_PATH = $out + [IO.Path]::PathSeparator + ($imports | Select-Object -Last 1)
    $env:LEAN_NUM_THREADS = '1'
    foreach ($name in (@($inputs.Keys) + $modules)) {
        & $lean -j1 -M3500 -DwarningAsError=true "--root=$stage" -o "$out/$name.olean" "$stage/$name.lean"
        $status = $LASTEXITCODE
        "$name exit=$status"
        if ($status -ne 0) { exit $status }
    }
} finally {
    Pop-Location
    $env:Path = $savedPath
    $env:LEAN_PATH = $savedLeanPath
    $env:LEAN_NUM_THREADS = $savedThreads
}
