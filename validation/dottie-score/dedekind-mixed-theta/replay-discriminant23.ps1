#Requires -Version 7.4
[CmdletBinding()]
param(
    [Parameter(Mandatory)] [string] $AxiomCheckout,
    [Parameter(Mandatory)] [string] $LeanBin,
    [ValidateRange(1, 8)] [int] $BuildThreads = 1
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
$sources = @(
    (Join-Path $repo 'lean-ideal73/DottieDyadicGeometry.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23Field.lean')
    (Join-Path $PSScriptRoot 'DedekindDiscriminant23Quadratic.lean')
    (Join-Path $PSScriptRoot 'DottieCompletedProductSign.lean')
    (Join-Path $PSScriptRoot 'Discriminant23ThetaEnvelope.lean')
    (Join-Path $PSScriptRoot 'DottieClassMellinBounds.lean')
    (Join-Path $PSScriptRoot 'Discriminant23DottieDisk.lean')
)
$importsNeeded = foreach ($source in $sources) {
    foreach ($line in (Get-Content -LiteralPath $source)) {
        if ($line -cmatch '^import (Mathlib\.[A-Za-z0-9._]+)$') {
            "+$($Matches[1]):olean"
        }
    }
}
$dependencies = @($importsNeeded | Sort-Object -Unique)
$out = (New-Item -ItemType Directory -Force -Path (Join-Path $checkout '.lake/super-zeta-discriminant23/lib')).FullName
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
        $sourceRoot = Split-Path -Parent $source
        $name = [IO.Path]::GetFileNameWithoutExtension($source)
        $blob = (& git hash-object --no-filters -- $source).Trim()
        "Super Zeta source $name $blob"
        & $lean "-j$BuildThreads" '-M6500' '-DwarningAsError=true' "--root=$sourceRoot" '-o' (Join-Path $out "$name.olean") $source
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
