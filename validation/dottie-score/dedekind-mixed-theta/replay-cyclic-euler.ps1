#Requires -Version 7.4
[CmdletBinding()]
param(
    [Parameter(Mandatory)] [string] $AxiomCheckout,
    [Parameter(Mandatory)] [string] $LeanBin,
    [ValidateRange(1, 8)] [int] $BuildThreads = 1,
    [switch] $GlobalDescent
)

$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [Text.Encoding]::UTF8
$root = (Resolve-Path -LiteralPath $AxiomCheckout).Path
$bin = (Resolve-Path -LiteralPath $LeanBin).Path
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

$replayName = if ($GlobalDescent) { 'super-zeta-cyclic-zeta-descent' } else { 'super-zeta-cyclic-euler' }
$out = (New-Item -ItemType Directory -Force -Path (Join-Path $root ".lake/$replayName/lib")).FullName
$modules = @(
    'DedekindCyclicSubgroupWeights'
    'DedekindUnramifiedFrobenius'
    'DedekindPrimeFiberCounting'
    'DedekindCyclicEulerCoefficients'
    'DedekindCyclicEulerFactors'
)
$dependencies = @(
    '+Mathlib.Algebra.BigOperators.Group.Finset.Sigma:olean'
    '+Mathlib.Combinatorics.Enumerative.IncidenceAlgebra:olean'
    '+Mathlib.Data.Fintype.WithTopBot:olean'
    '+Mathlib.FieldTheory.Finite.Basic:olean'
    '+Mathlib.GroupTheory.SpecificGroups.Cyclic:olean'
    '+Mathlib.NumberTheory.Divisors:olean'
    '+Mathlib.NumberTheory.NumberField.Ideal.Basic:olean'
    '+Mathlib.NumberTheory.RamificationInertia.Galois:olean'
    '+Mathlib.RingTheory.Frobenius:olean'
    '+Mathlib.Tactic.Linarith:olean'
)
if ($GlobalDescent) {
    $modules += @(
        'DedekindFiniteRamification'
        'DedekindCyclicZetaLocal'
        'DedekindCyclicZetaProducts'
        'DedekindCyclicZetaDescent'
        'DedekindGaloisDottieTarget'
    )
    $dependencies += @(
        '+DedekindZetaZeroFree.LFunctions.Dedekind.EulerProductRegrouping:olean'
        '+Mathlib.Algebra.Group.Units.Hom:olean'
        '+Mathlib.Analysis.SpecialFunctions.Pow.Deriv:olean'
        '+Mathlib.RingTheory.DedekindDomain.Different:olean'
    )
}

$oldPath = $env:Path
$oldLeanPath = $env:LEAN_PATH
$oldThreads = $env:LEAN_NUM_THREADS
$separator = [IO.Path]::PathSeparator
$pwsh = (Get-Command pwsh).Source
try {
    $env:Path = $bin + $separator + $oldPath
    $env:LEAN_NUM_THREADS = [string] $BuildThreads
    if ($GlobalDescent) {
        & $pwsh -NoLogo -NoProfile -NonInteractive -File (Join-Path $PSScriptRoot 'replay.ps1') `
            -AxiomCheckout $root -LeanBin $bin -BuildThreads $BuildThreads -RelativeDottie
        if ($LASTEXITCODE -ne 0) { throw 'Relative Dottie replay failed.' }
    }
    & $lake -d $root build @dependencies
    if ($LASTEXITCODE -ne 0) { throw 'Lake dependency build failed.' }

    $imports = & $lake -d $root env $pwsh -NoLogo -NoProfile -NonInteractive -Command '$env:LEAN_PATH'
    if ($LASTEXITCODE -ne 0 -or !$imports) { throw 'Could not read the Lake import path.' }
    $importPaths = @($out)
    if ($GlobalDescent) { $importPaths += Join-Path $root '.lake/super-zeta-relative-dottie/lib' }
    $importPaths += $imports | Select-Object -Last 1
    $env:LEAN_PATH = $importPaths -join $separator

    foreach ($name in $modules) {
        $file = Join-Path $PSScriptRoot "$name.lean"
        $blob = (& git hash-object --no-filters -- $file).Trim()
        "Super Zeta source $name $blob"
        $memory = if ($name -in @('DedekindCyclicZetaProducts', 'DedekindCyclicZetaDescent', 'DedekindGaloisDottieTarget')) {
            6000
        } else {
            3300
        }
        & $lean "-j$BuildThreads" "-M$memory" '-DwarningAsError=true' "--root=$PSScriptRoot" '-o' (Join-Path $out "$name.olean") $file
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
