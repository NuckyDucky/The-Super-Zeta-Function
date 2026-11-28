#Requires -Version 7.4
[CmdletBinding()]
param(
    [Parameter(Mandatory)] [string] $Lean,
    [Parameter(Mandatory)] [string] $OutputDirectory,
    [string[]] $Imports = @()
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
$modules = [ordered]@{
    DedekindDiscriminant23Height29Polynomials = 2
    DottieGaussianPolynomial = 6
    DedekindDiscriminant23Height29ExactBounds = 5
}

try {
    $env:LEAN_PATH = ((@($output) + @($importPaths) + @($oldLeanPath)) | Where-Object { $_ }) -join [IO.Path]::PathSeparator
    $env:LEAN_NUM_THREADS = '1'
    $version
    foreach ($module in $modules.Keys) {
        $source = Join-Path $PSScriptRoot "$module.lean"
        $object = Join-Path $output "$module.olean"
        $blob = & git hash-object --no-filters -- $source
        if ($LASTEXITCODE -ne 0) { throw "Could not hash $module." }
        "Super Zeta source $module $blob"
        $result = & $leanExe '-j1' '-s32768' '-M5000' '-DwarningAsError=true' "--root=$PSScriptRoot" '-o' $object $source 2>&1
        $status = $LASTEXITCODE
        $result
        "$module exit=$status"
        if ($status -ne 0) { throw "$module failed." }
        $reports = [regex]::Matches(($result -join "`n"), 'depends on axioms:\s*\[([^\]]*)\]')
        if ($reports.Count -ne $modules[$module]) { throw "Missing axiom reports for $module." }
        foreach ($report in $reports) {
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
