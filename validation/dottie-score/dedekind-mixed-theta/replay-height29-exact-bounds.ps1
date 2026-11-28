#Requires -Version 7.4
[CmdletBinding()]
param(
    [Parameter(Mandatory)] [string] $Lean,
    [Parameter(Mandatory)] [string] $OutputDirectory,
    [string[]] $Imports = @(),
    [switch] $CircleSamples,
    [switch] $FactorQuadrature
)

$ErrorActionPreference = 'Stop'
$leanExe = (Resolve-Path -LiteralPath $Lean).Path
$version = & $leanExe --version
if ($LASTEXITCODE -ne 0 -or $version -notmatch '470d5ce1400764999581fd26d5d72b00d990b0f4') {
    throw 'Use the pinned Lean 4.35.0-rc3 toolchain.'
}

$output = (New-Item -ItemType Directory -Force -Path $OutputDirectory).FullName
$importPaths = foreach ($item in $Imports) { (Resolve-Path -LiteralPath $item).Path }
$oldLeanPath = $env:LEAN_PATH
$oldThreads = $env:LEAN_NUM_THREADS
$modules = [ordered]@{}
if ($FactorQuadrature) { $modules.Add('Discriminant23ThetaEnvelope', 8) }
if ($CircleSamples) {
    $modules.Add('DottieClassMellinBounds', 6)
    $modules.Add('Discriminant23DottieDisk', 6)
    $modules.Add('DedekindDiscriminant23DottieReading', 16)
    $modules.Add('DedekindWideOuterDottie', 2)
}
if (!$FactorQuadrature -or $CircleSamples) {
    $base = [ordered]@{
        DedekindDiscriminant23Height29Polynomials = 2
        DottieGaussianPolynomial = 6
        DedekindDiscriminant23Height29ExactBounds = 7
    }
    foreach ($module in $base.Keys) { $modules.Add($module, $base[$module]) }
}
if ($CircleSamples) {
    $modules.Add('DedekindDiscriminant23Height29FourierError', 3)
    $modules.Add('DedekindDiscriminant23Height29CircleCertificate', 7)
    $modules.Add('ContourGaussianDFT', 5)
    $modules.Add('ContourRoot128', 3)
    $modules.Add('DedekindDiscriminant23Height29Samples', 1)
    foreach ($block in 0..22) { $modules.Add(('Height29DFTSum.Block{0:D2}' -f $block), 1) }
    $modules.Add('DedekindDiscriminant23Height29DFT', 2)
}
if ($FactorQuadrature) {
    $modules.Add('ComplexMellinFoldEstimates', 4)
    $modules.Add('RationalPanelQuadrature', 4)
    $modules.Add('Gauss24PanelTable', 4)
    $modules.Add('Discriminant23ClassMellinTruncation', 3)
    $modules.Add('Discriminant23ClassMellinGauss', 3)
    $modules.Add('DedekindDiscriminant23Height29FactorEnclosures', 1)
    $modules.Add('DedekindDiscriminant23Height29QuadratureCertificate', 4)
}

try {
    $env:LEAN_PATH = ((@($output) + @($importPaths) + @($oldLeanPath)) | Where-Object { $_ }) -join [IO.Path]::PathSeparator
    $env:LEAN_NUM_THREADS = '1'
    $version
    foreach ($module in $modules.Keys) {
        $modulePath = $module.Replace('.', '/')
        $source = Join-Path $PSScriptRoot "$modulePath.lean"
        $object = Join-Path $output "$modulePath.olean"
        $null = New-Item -ItemType Directory -Force -Path (Split-Path -Parent $object)
        $blob = & git hash-object --no-filters -- $source
        if ($LASTEXITCODE -ne 0) { throw "Could not hash $module." }
        "Super Zeta source $module $blob"
        $result = & $leanExe '-j1' '-s32768' '-M5000' '-DwarningAsError=true' "--root=$PSScriptRoot" '-o' $object $source 2>&1
        $status = $LASTEXITCODE
        $result
        "$module exit=$status"
        if ($status -ne 0) { throw "$module failed." }
        $reports = [regex]::Matches(($result -join "`n"), 'depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms')
        if ($reports.Count -ne $modules[$module]) { throw "Missing axiom reports for $module." }
        foreach ($report in $reports) {
            if (!$report.Groups[1].Success) { continue }
            $axioms = $report.Groups[1].Value -split ',\s*' | ForEach-Object { $_.Trim() }
            if ($axioms | Where-Object { $_ -notin @('propext', 'Classical.choice', 'Quot.sound') }) {
                throw "Unexpected axiom in $module."
            }
        }
    }
}
finally {
    $env:LEAN_PATH = $oldLeanPath
    $env:LEAN_NUM_THREADS = $oldThreads
}
