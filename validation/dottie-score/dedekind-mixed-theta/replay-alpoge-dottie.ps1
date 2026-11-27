#Requires -Version 7.4
param(
    [Parameter(Mandatory)] [string] $AxiomCheckout,
    [Parameter(Mandatory)] [string] $LeanBin,
    [Parameter(Mandatory)] [string] $AlpogeSource
)

$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [Text.Encoding]::UTF8
$root = (Resolve-Path -LiteralPath $AxiomCheckout).Path
$bin = (Resolve-Path -LiteralPath $LeanBin).Path
$alpoge = (Resolve-Path -LiteralPath $AlpogeSource).Path
$suffix = if ($IsWindows) { '.exe' } else { '' }
$lean = Join-Path $bin ('lean' + $suffix)
$lake = Join-Path $bin ('lake' + $suffix)
$version = & $lean --version
$head = (& git -C $root rev-parse HEAD).Trim()
$mathlib = (& git -C (Join-Path $root '.lake/packages/mathlib') rev-parse HEAD).Trim()
if ($head -ne '09afbb4ce6570c1615d58509dc197fc9f0956b7d' -or
    $mathlib -ne '0493595ecd5da8ef14742febab99728f98e948e8' -or
    $version -notmatch '470d5ce1400764999581fd26d5d72b00d990b0f4') {
    throw 'Use the pinned AxiomMath sources, Mathlib, and Lean 4.35.0-rc3.'
}
$version
"AxiomMath $head"
"Mathlib $mathlib"

$base = Join-Path $root '.lake/super-zeta-sampled-contours/lib'
foreach ($name in @('DottieContourPhase', 'DottieRationalContour', 'DedekindMixedThetaCompletedRings')) {
    if (!(Test-Path -LiteralPath (Join-Path $base "$name.olean"))) {
        throw 'Run replay.ps1 with -SampledContours before this replay.'
    }
}
$stage = (New-Item -ItemType Directory -Force -Path "$root/.lake/super-zeta-alpoge-dottie/src").FullName
$out = (New-Item -ItemType Directory -Force -Path "$root/.lake/super-zeta-alpoge-dottie/lib").FullName
$folder = 'Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds'
$sourceDir = (New-Item -ItemType Directory -Force -Path "$stage/$folder").FullName
$outputDir = (New-Item -ItemType Directory -Force -Path "$out/$folder").FullName
$upstream = [ordered]@{
    NormCpowSubLePoint = '1aeedcff2f9bc6aa196465c72936661ec2403883'
    DzDifferentiableOn = '3123f36de19d54f6f6fd76f465b99e1ce630e03b'
    RiemannZetaOneEqOneSubOfRePos = '482dcb937bc1460df0b85615adcaee8005c1e077'
    ZetaGrowth = '76e0bbd075fd8ea6acf5edff73196e01416e726c'
    ZfoGrowthBall = 'bbc0433ff6f3ef0a48cb0cdae925238f1fb11b20'
}
$growth = '∀ s : ℂ, 0 < s.re → s ≠ 1 → ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)'
$inverse = '∀ s : ℂ, 1 < s.re → ‖riemannZeta s‖⁻¹ ≤ s.re / (s.re - 1)'
$smallHeight = 'import Formalism.ZeroFreeRegion.SmallHeightLogDeriv'
$savedPath = $env:Path
$savedLeanPath = $env:LEAN_PATH
$savedThreads = $env:LEAN_NUM_THREADS
$env:Path = $bin + [IO.Path]::PathSeparator + $env:Path
$env:LEAN_NUM_THREADS = '1'

function Build-AuditedModule([string] $Name, [string] $Source, [string] $Output) {
    "$Name source $(& git hash-object --no-filters -- $Source)"
    & $lean -j1 -M3500 -DwarningAsError=true "--root=$stage" -o $Output $Source
    $status = $LASTEXITCODE
    "$Name exit=$status"
    if ($status -ne 0) { exit $status }
}

Push-Location -LiteralPath $root
try {
    $runtime = (Get-Command pwsh).Source
    $imports = & $lake env $runtime -NoLogo -NoProfile -NonInteractive -Command '$env:LEAN_PATH'
    if ($LASTEXITCODE -ne 0 -or !$imports) { throw 'Could not determine the pinned Lake import path.' }
    $env:LEAN_PATH = @($out, $base, ($imports | Select-Object -Last 1)) -join [IO.Path]::PathSeparator
    foreach ($name in $upstream.Keys) {
        $source = Join-Path $alpoge "src/$folder/$name.lean"
        $sha = (& git hash-object --no-filters -- $source).Trim()
        if ($LASTEXITCODE -ne 0 -or $sha -ne $upstream[$name]) { throw "$name differs from the pinned Alpöge source." }
        "Alpöge source $name $sha"
        $code = [IO.File]::ReadAllText($source).Replace('if_neg', 'ite_eq_right')
        if ($name -eq 'ZetaGrowth') {
            $code = $code -replace "(?m)^$([regex]::Escape($smallHeight))\r?\n", ''
            $code = $code.Replace('theorem growthBound : ZetaGrowth := by', "theorem growthBound : $growth := by")
        }
        if ($name -eq 'ZfoGrowthBall') {
            $code = $code.Replace($smallHeight, 'import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth')
            $code = $code.Replace('(hG : ZetaGrowth)', "(hG : $growth)").Replace('(hI : ZetaInvBound)', "(hI : $inverse)")
        }
        $target = Join-Path $sourceDir "$name.lean"
        [IO.File]::WriteAllText($target, $code, [Text.UTF8Encoding]::new($false))
        Build-AuditedModule $name $target (Join-Path $outputDir "$name.olean")
    }
    $modules = @(
        'ContourTaylor', 'ContourCircleSamples', 'DottieCayleyWeightedRiemann', 'DottieCayleySameInput',
        'DottieCayleySamplePolynomial', 'DottieCayleyGrowthBridge', 'DottieCandidateCircles',
        'DottieNearOneDisk', 'DottieAlpogeDisk', 'DottieNativeCandidate', 'DottieNativeExclusion',
        'DedekindMixedThetaSampleModel', 'ContourExponentialModel'
    )
    foreach ($name in $modules) {
        $target = Join-Path $stage "$name.lean"
        Copy-Item -LiteralPath (Join-Path $PSScriptRoot "$name.lean") -Destination $target
        Build-AuditedModule $name $target (Join-Path $out "$name.olean")
    }
} finally {
    Pop-Location
    $env:Path = $savedPath
    $env:LEAN_PATH = $savedLeanPath
    $env:LEAN_NUM_THREADS = $savedThreads
}
