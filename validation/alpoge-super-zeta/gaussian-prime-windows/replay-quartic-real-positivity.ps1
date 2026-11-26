#Requires -Version 7.4
param(
    [Parameter(Mandatory)] [string] $LeanExecutable,
    [Parameter(Mandatory)] [string] $QuarticKernelLibrary,
    [Parameter(Mandatory)] [string] $MathlibPackages,
    [string] $OutputDirectory
)

$ErrorActionPreference = 'Stop'
$lean = (Resolve-Path -LiteralPath $LeanExecutable).Path
$quartic = (Resolve-Path -LiteralPath $QuarticKernelLibrary).Path
$packages = (Resolve-Path -LiteralPath $MathlibPackages).Path
$mathlibPin = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'

$version = & $lean --version
if ($LASTEXITCODE -ne 0 -or $version -notmatch 'version 4\.19\.0,.*6caaee842e94') {
    throw "Use the pinned Lean 4.19.0 executable. Found $version"
}
$revision = & git -C "$packages/mathlib" rev-parse HEAD
if ($LASTEXITCODE -ne 0 -or $revision -ne $mathlibPin) {
    throw "The Mathlib checkout must be at $mathlibPin."
}
if (!(Test-Path -LiteralPath "$quartic/QuarticCheckedShellKernel.olean")) {
    throw 'Run the quartic kernel replay and supply its compiled checkpoint.'
}

$version
"Mathlib $revision"
if (!$OutputDirectory) {
    $suffix = [Guid]::NewGuid().ToString('N').Substring(0, 12)
    $OutputDirectory = Join-Path ([IO.Path]::GetTempPath()) "qreal-$suffix"
}
$out = (New-Item -ItemType Directory -Path $OutputDirectory -Force).FullName
$libraries = Get-ChildItem -Directory -LiteralPath $packages |
    ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' } |
    Where-Object { Test-Path -LiteralPath $_ }

$savedPath = $env:LEAN_PATH
$savedThreads = $env:LEAN_NUM_THREADS
try {
    $env:LEAN_PATH = (@($out, $quartic) + $libraries) -join [IO.Path]::PathSeparator
    $env:LEAN_NUM_THREADS = '1'
    foreach ($module in @('QuarticRealFormula', 'QuarticPositiveReal')) {
        $module
        & $lean -j1 '-DwarningAsError=true' "--root=$PSScriptRoot" -o "$out/$module.olean" "$PSScriptRoot/$module.lean"
        $status = $LASTEXITCODE
        "exit=$status"
        if ($status -ne 0) { throw "Lean failed for $module." }
    }
}
finally {
    $env:LEAN_PATH = $savedPath
    $env:LEAN_NUM_THREADS = $savedThreads
}
