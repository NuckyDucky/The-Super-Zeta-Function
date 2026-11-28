#Requires -Version 7.4
[CmdletBinding()]
param(
    [Parameter(Mandatory)] [string] $AxiomCheckout,
    [Parameter(Mandatory)] [string] $LeanBin,
    [Parameter(Mandatory)] [string] $HuCacheRoot,
    [string[]] $RayHeckeImports = @(),
    [string[]] $Discriminant23Imports = @(),
    [switch] $Discriminant23TwentyCount,
    [switch] $Discriminant23RightBandCount
)

$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [Text.Encoding]::UTF8
$axiom = (Resolve-Path -LiteralPath $AxiomCheckout).Path
$hu = (Resolve-Path -LiteralPath $HuCacheRoot).Path
$bin = (Resolve-Path -LiteralPath $LeanBin).Path
$suffix = if ($IsWindows) { '.exe' } else { '' }
$lean = Join-Path $bin "lean$suffix"
$lake = Join-Path $bin "lake$suffix"
$version = & $lean --version
$axiomRev = (& git -C $axiom rev-parse HEAD).Trim()
$mathlibRev = (& git -C (Join-Path $axiom '.lake/packages/mathlib') rev-parse HEAD).Trim()
if ($axiomRev -ne '09afbb4ce6570c1615d58509dc197fc9f0956b7d' -or
    $mathlibRev -ne '0493595ecd5da8ef14742febab99728f98e948e8' -or
    $version -notmatch '470d5ce1400764999581fd26d5d72b00d990b0f4') {
    throw 'Use the pinned AxiomMath checkout, Mathlib, and Lean 4.35.0-rc3.'
}

$huLibraries = @(
    (Join-Path $hu '.lake/build/lib/lean')
    (Join-Path $hu 'vendor/class-field-theory/.lake/build/lib/lean')
    (Join-Path $hu '.lake/packages/TauCeti/.lake/build/lib/lean')
)
$solution = Join-Path $huLibraries[0] 'HeckeSevenEighthsSolution.olean'
$solutionHash = (Get-FileHash -LiteralPath $solution -Algorithm SHA256).Hash
if ($RayHeckeImports.Count -eq 0) {
    $RayHeckeImports = @(
        (Join-Path $axiom '.lake/super-zeta-ray-hecke/lib')
        (Join-Path $axiom '.lake/super-zeta-cyclic-zeta-descent/lib')
        (Join-Path $axiom '.lake/super-zeta-relative-dottie/lib')
    )
}
$baseline = foreach ($path in $RayHeckeImports) { (Resolve-Path -LiteralPath $path).Path }
if ($Discriminant23RightBandCount) { $Discriminant23TwentyCount = $true }
if ($Discriminant23TwentyCount -and $Discriminant23Imports.Count -eq 0) {
    $Discriminant23Imports = @((Join-Path $axiom '.lake/super-zeta-higher-polynomial-bands/lib'))
}
$characterImports = @(
    foreach ($path in $Discriminant23Imports) { (Resolve-Path -LiteralPath $path).Path }
)
$out = (New-Item -ItemType Directory -Force -Path (
    Join-Path $axiom '.lake/super-zeta-hecke-seven-eighths/lib')).FullName
$separator = [IO.Path]::PathSeparator
$pwsh = (Get-Command pwsh).Source
$oldPath = $env:Path
$oldLeanPath = $env:LEAN_PATH
$oldThreads = $env:LEAN_NUM_THREADS
$version
"AxiomMath $axiomRev"
"Mathlib $mathlibRev"
"Hu solution object SHA-256 $solutionHash"

try {
    $env:Path = $bin + $separator + $oldPath
    $env:LEAN_NUM_THREADS = '1'
    if ($Discriminant23RightBandCount) {
        $starDeriv = Join-Path $axiom '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Calculus/Deriv/Star.olean'
        if (!(Test-Path -LiteralPath $starDeriv)) {
            & $lake -d $axiom build '+Mathlib.Analysis.Calculus.Deriv.Star:olean'
            if ($LASTEXITCODE -ne 0) { throw 'Could not build the Mathlib derivative reflection lemma.' }
        }
    }
    $imports = & $lake -d $axiom env $pwsh -NoLogo -NoProfile -NonInteractive -Command '$env:LEAN_PATH'
    if ($LASTEXITCODE -ne 0 -or !$imports) { throw 'Could not read the Lake import path.' }

    # The release supplies a few shared base modules absent from the AxiomMath cache.
    # Use its whole base namespace for all five source replays.
    $env:LEAN_PATH = ($huLibraries + @($out) + $baseline + @($imports | Select-Object -Last 1)) -join $separator
    $modules = [ordered]@{
        RayHeckeStripCounts = 6
        RayHeckeDedekindTransfer = 7
        RayHeckeRightBand = 3
        HeckeSevenEighthsTransfer = 6
        DedekindSevenEighthsCoverage = 3
    }
    if ($characterImports.Count -gt 0) {
        $modules.Add('DedekindDiscriminant23SevenEighths', 2)
        $modules.Add('DedekindDiscriminant23TaylorRadiusCeiling', 1)
        $modules.Add('ComplexStripCrossingMesh', 3)
        $modules.Add('DedekindDiscriminant23TwentyBand', 4)
    }
    if ($Discriminant23TwentyCount) {
        $modules.Add('Gauss23SharedCoefficients', 4)
        $modules.Add('Gauss23UnitPhaseTable', 2)
        $modules.Add('Gauss23CoefficientTable', 1)
        $modules.Add('Gauss23CenteredHorner', 1)
        $modules.Add('Gauss23RectangleCover', 3)
        $modules.Add('Gauss23TwentyCell', 1)
        $modules.Add('Gauss23TwentyGrid', 1)
        $modules.Add('Gauss23TwentyValues', 0)
        foreach ($height in 10..20) {
            $modules.Add("Gauss23Height${height}Values", 1)
            $modules.Add("Gauss23Height${height}Cover", 1)
        }
        $modules.Add('DedekindDiscriminant23TwentyCount', 6)
    }
    if ($Discriminant23RightBandCount) {
        $modules.Add('Gauss23StripReflection', 2)
        $modules.Add('DedekindDiscriminant23RightStripCount', 2)
        $modules.Add('Gauss23RightBandCell', 1)
        $modules.Add('Gauss23RightValues', 1)
        $modules.Add('Gauss23RightMesh', 1)
        foreach ($height in 20..28) {
            if ($height -gt 20) { $modules.Add("Gauss23Height${height}Values", 1) }
            $modules.Add("Gauss23Height${height}RightCover", 1)
        }
        $modules.Add('DedekindDiscriminant23RightBandCount', 5)
    }
    foreach ($name in $modules.Keys) {
        if ($name -eq 'DedekindDiscriminant23SevenEighths') {
            # Use the higher-band factorization ahead of any earlier cached copy.
            $env:LEAN_PATH = ($huLibraries + @($out) + $characterImports + $baseline +
                @($imports | Select-Object -Last 1)) -join $separator
        }
        $source = Join-Path $PSScriptRoot "$name.lean"
        $blob = (& git hash-object --no-filters -- $source).Trim()
        "Super Zeta source $name $blob"
        $object = Join-Path $out "$name.olean"
        $stack = @(if ($name -like 'Gauss23*' -or $name -in @(
            'DedekindDiscriminant23TwentyCount', 'DedekindDiscriminant23RightStripCount',
            'DedekindDiscriminant23RightBandCount')) {
            '-s32768'
        })
        $report = & $lean '-j1' @stack '-M7500' '-DwarningAsError=true' "--root=$PSScriptRoot" '-o' $object $source 2>&1
        $status = $LASTEXITCODE
        $report
        "$name exit=$status"
        if ($status -ne 0) { throw "$name failed." }
        $reports = [regex]::Matches(($report -join "`n"), 'depends on axioms:\s*\[([^\]]*)\]')
        if ($reports.Count -ne $modules[$name]) { throw "Missing axiom reports for $name." }
        foreach ($entry in $reports) {
            $axioms = $entry.Groups[1].Value -split ',\s*' | ForEach-Object { $_.Trim() }
            if ($axioms | Where-Object { $_ -notin @('propext', 'Classical.choice', 'Quot.sound') }) {
                throw "Unexpected axiom in $name."
            }
        }
    }
}
finally {
    $env:Path = $oldPath
    $env:LEAN_PATH = $oldLeanPath
    $env:LEAN_NUM_THREADS = $oldThreads
}
