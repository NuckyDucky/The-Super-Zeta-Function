#Requires -Version 7.4
[CmdletBinding()]
param(
    [Parameter(Mandatory)] [string] $AxiomCheckout,
    [Parameter(Mandatory)] [string] $LeanBin,
    [ValidateRange(1, 8)] [int] $BuildThreads = 1,
    [switch] $DirichletMod23,
    [switch] $CharacterBracket,
    [switch] $ComplexDerivatives,
    [switch] $CharacterQuadrature,
    [switch] $CharacterCount
)

$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [Text.Encoding]::UTF8
$checkout = (Resolve-Path -LiteralPath $AxiomCheckout).Path
$bin = (Resolve-Path -LiteralPath $LeanBin).Path
$suffix = if ($IsWindows) { '.exe' } else { '' }
$lean = Join-Path $bin ('lean' + $suffix)
$lake = Join-Path $bin ('lake' + $suffix)
$head = (& git -C $checkout rev-parse HEAD).Trim()
$mathlib = (& git -C (Join-Path $checkout '.lake/packages/mathlib') rev-parse HEAD).Trim()
$version = & $lean --version
if ($head -ne '09afbb4ce6570c1615d58509dc197fc9f0956b7d' -or
    $mathlib -ne '0493595ecd5da8ef14742febab99728f98e948e8' -or
    $version -notmatch '470d5ce1400764999581fd26d5d72b00d990b0f4') {
    throw 'Use the pinned AxiomMath checkout, Mathlib, and Lean 4.35.0-rc3.'
}
$version
"AxiomMath $head"
"Mathlib $mathlib"

$repo = Join-Path $PSScriptRoot '../../..'
if ($CharacterCount) {
    $CharacterQuadrature = $true
}
if ($CharacterQuadrature) {
    $ComplexDerivatives = $true
}
if ($ComplexDerivatives) {
    $CharacterBracket = $true
}
if ($CharacterBracket) {
    $DirichletMod23 = $true
}
$sources = @(
    (Join-Path $repo 'lean-ideal73/DottieDyadicGeometry.lean')
    (Join-Path $repo 'lean-ideal73/FieldTarget.lean')
    (Join-Path $repo 'lean-ideal73/DedekindDottieSetup.lean')
    (Join-Path $repo 'lean-ideal73/DedekindFieldInputs.lean')
    (Join-Path $repo 'lean-ideal73/DedekindFieldUniverses.lean')
    (Join-Path $repo 'lean-ideal73/DedekindFiniteDottieCover.lean')
    (Join-Path $repo 'lean-ideal73/DedekindCofinalSignedRings.lean')
    (Join-Path $PSScriptRoot 'DedekindMixedTheta.lean')
    (Join-Path $PSScriptRoot 'DedekindMixedThetaSignedRings.lean')
    (Join-Path $PSScriptRoot 'DedekindFiniteStripCounts.lean')
    (Join-Path $PSScriptRoot 'DedekindMixedThetaTail.lean')
    (Join-Path $PSScriptRoot 'DedekindMixedThetaCompletedRings.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23Field.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23Quadratic.lean')
    (Join-Path $PSScriptRoot 'DottieCompletedProductSign.lean')
    (Join-Path $PSScriptRoot 'Discriminant23ThetaEnvelope.lean')
    (Join-Path $PSScriptRoot 'DottieClassMellinBounds.lean')
    (Join-Path $PSScriptRoot 'Discriminant23DottieDisk.lean')
    (Join-Path $PSScriptRoot 'DedekindUnramifiedFrobenius.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23Unramified.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23Integers.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23NormForms.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23ClassRepresentatives.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23ClassNumber.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23Hilbert.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23EulerProduct.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23ClassSeries.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23ClassTheta.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23ThetaForms.lean')
    (Join-Path $PSScriptRoot 'DedekindIdealClassThetaPair.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23ThetaProfiles.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23CompletedProduct.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23DottieReading.lean')
)
if ($DirichletMod23) {
    $sources += @(
        (Join-Path $PSScriptRoot 'DedekindRationalPrimeFibers.lean')
        (Join-Path $PSScriptRoot 'DedekindEulerByRationalPrime.lean')
        (Join-Path $PSScriptRoot 'DedekindCyclotomicLocalEuler.lean')
        (Join-Path $PSScriptRoot 'DedekindCyclotomicContinuation.lean')
        (Join-Path $PSScriptRoot 'DedekindCyclotomicSubfields.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23DirichletReduction.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23ZeroCounts.lean')
    )
}
if ($CharacterBracket) {
    $intervalRoot = Join-Path $repo 'validation/alpoge-super-zeta'
    $sources += @(
        (Join-Path $intervalRoot 'MellinFixedInterval.lean')
        (Join-Path $intervalRoot 'MellinFixedFunctions.lean')
        (Join-Path $intervalRoot 'MellinFixedIntervalSound.lean')
        (Join-Path $intervalRoot 'MellinFixedElementary.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterPolynomial.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterIntegral.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterQuadrature.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterSamples.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterGrid.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterGridLower.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterGridUpper.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterBracket.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterReflectedCounts.lean')
    )
}
if ($ComplexDerivatives) {
    $sources += @(
        (Join-Path $PSScriptRoot 'ComplexMellinFoldEstimates.lean')
        (Join-Path $PSScriptRoot 'DedekindMixedThetaDerivative.lean')
        (Join-Path $PSScriptRoot 'DedekindMixedThetaMultiplicity.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterComplex.lean')
        (Join-Path $PSScriptRoot 'ComplexStripSingleZero.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CountFromSigns.lean')
    )
}
if ($CharacterQuadrature) {
    $sources += @(
        (Join-Path $PSScriptRoot 'ContourTaylor.lean')
        (Join-Path $PSScriptRoot 'ComplexNewtonCotes.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterPanel.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterSparse.lean')
    )
}
if ($CharacterCount) {
    $sources += @(
        (Join-Path $PSScriptRoot 'FoldedExponentialTaylor.lean')
        (Join-Path $PSScriptRoot 'NinePointGrid.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CharacterMoments.lean')
        (Join-Path $PSScriptRoot 'MellinFixedComplexPolynomial.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23ReadingIntervals.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23AmplitudeData.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CoefficientData.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23ReadingCells.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23ReadingTail.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23ReadingCover.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23BelowCellSigns.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23SlopeCellSigns.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23AboveCellSigns.lean')
        (Join-Path $PSScriptRoot 'DedekindDiscriminant23CountCertificate.lean')
    )
}
$legacyPiModule = 'Mathlib.Data.Real.Pi.Bounds'
$pinnedPiModule = 'Mathlib.Analysis.Real.Pi.Bounds'
$importsNeeded = foreach ($source in $sources) {
    foreach ($line in (Get-Content -LiteralPath $source)) {
        if ($line -cmatch '^import ((?:Mathlib|ClassFieldTheory|DedekindZetaZeroFree)\.[A-Za-z0-9._]+)$') {
            $module = $Matches[1]
            if ($CharacterBracket -and $module -ceq $legacyPiModule) { $module = $pinnedPiModule }
            "+${module}:olean"
        }
    }
}
$dependencies = @($importsNeeded | Sort-Object -Unique)
$libraryPath = if ($CharacterCount) {
    '.lake/super-zeta-discriminant23-character-count/lib'
} elseif ($CharacterBracket) {
    '.lake/super-zeta-discriminant23-character-bracket/lib'
} elseif ($DirichletMod23) {
    '.lake/super-zeta-discriminant23-mod23/lib'
} else {
    '.lake/super-zeta-discriminant23/lib'
}
$out = (New-Item -ItemType Directory -Force -Path (Join-Path $checkout $libraryPath)).FullName
$oldPath = $env:Path
$oldLeanPath = $env:LEAN_PATH
$oldThreads = $env:LEAN_NUM_THREADS
$separator = [IO.Path]::PathSeparator
$pwsh = (Get-Command pwsh).Source
try {
    $env:Path = $bin + $separator + $oldPath
    $env:LEAN_NUM_THREADS = [string] $BuildThreads
    & $lake -d $checkout build @dependencies
    if ($LASTEXITCODE -ne 0) { throw 'Lake dependency build failed.' }
    $imports = & $lake -d $checkout env $pwsh -NoLogo -NoProfile -NonInteractive -Command '$env:LEAN_PATH'
    if ($LASTEXITCODE -ne 0 -or !$imports) { throw 'Could not read the Lake import path.' }
    $env:LEAN_PATH = $out + $separator + ($imports | Select-Object -Last 1)

    foreach ($path in $sources) {
        $source = (Resolve-Path -LiteralPath $path).Path
        $name = [IO.Path]::GetFileNameWithoutExtension($source)
        $blob = (& git hash-object --no-filters -- $source).Trim()
        "Super Zeta source $name $blob"
        if ($CharacterBracket -and $name -ceq 'MellinFixedElementary') {
            $sourceText = [IO.File]::ReadAllText($source)
            $oldImport = '(?m)^' + [regex]::Escape("import $legacyPiModule") + '(?=\r?$)'
            if ([regex]::Matches($sourceText, $oldImport).Count -ne 1) {
                throw 'Expected one legacy Mathlib pi-bounds import.'
            }
            $sourceDir = New-Item -ItemType Directory -Force -Path (Join-Path $out 'sources')
            $source = Join-Path $sourceDir.FullName "$name.lean"
            [IO.File]::WriteAllText($source, ($sourceText -creplace $oldImport, "import $pinnedPiModule"))
            $replayBlob = (& git hash-object --no-filters -- $source).Trim()
            "Pinned pi-bounds import replay $name $replayBlob"
        }
        $sourceRoot = Split-Path -Parent $source
        $object = Join-Path $out "$name.olean"
        & $lean "-j$BuildThreads" '-M6500' '-DwarningAsError=true' "--root=$sourceRoot" '-o' $object $source
        $status = $LASTEXITCODE
        "$name exit=$status"
        if ($status -ne 0) { throw "$name failed." }
    }
}
finally {
    $env:Path = $oldPath
    $env:LEAN_PATH = $oldLeanPath
    $env:LEAN_NUM_THREADS = $oldThreads
}
