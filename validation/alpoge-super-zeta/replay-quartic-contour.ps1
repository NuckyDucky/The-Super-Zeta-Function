#Requires -Version 7.4
param(
    [Parameter(Mandatory)] [string] $AlpogeCheckout,
    [Parameter(Mandatory)] [string] $LeanExecutable,
    [Parameter(Mandatory)] [string] $QuarticLibrary,
    [Parameter(Mandatory)] [string] $MathlibPackages,
    [string] $OutputDirectory
)

$ErrorActionPreference = 'Stop'
$packet = $PSScriptRoot
$lean = (Resolve-Path -LiteralPath $LeanExecutable).Path
$quartic = (Resolve-Path -LiteralPath $QuarticLibrary).Path
$checkout = (Resolve-Path -LiteralPath $AlpogeCheckout).Path
$packages = (Resolve-Path -LiteralPath $MathlibPackages).Path
$pin = 'ba2a065656ec7c638baa601994de3e0245ff6665'
$mathlibPin = '0df444a360eaa60ab8c11dca51a86af692955474'

$version = & $lean --version
if ($LASTEXITCODE -ne 0 -or $version -notmatch '819816b2e0a3bf405af45ae5c7af2491d8f5bee6') {
    throw "Use the pinned Lean 4.33.1 binary. Found $version"
}
$revision = & git -C "$packages/mathlib" rev-parse HEAD
if ($LASTEXITCODE -ne 0 -or $revision -ne $mathlibPin) {
    throw "The Mathlib checkout must be at $mathlibPin."
}
$version
"Mathlib $revision"
"Alpöge $pin"
if (!$OutputDirectory) {
    $suffix = [Guid]::NewGuid().ToString('N').Substring(0, 12)
    $OutputDirectory = Join-Path ([IO.Path]::GetTempPath()) "qc-$suffix"
}
$out = (New-Item -ItemType Directory -Path $OutputDirectory -Force).FullName
$upstream = (New-Item -ItemType Directory -Path "$out/upstream" -Force).FullName
$group = 'GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets'
New-Item -ItemType Directory -Path "$upstream/$group" -Force | Out-Null
$libraries = Get-ChildItem -Directory -LiteralPath $packages |
    ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' } |
    Where-Object { Test-Path -LiteralPath $_ }

function Invoke-LeanBuild([string] $Source, [string] $Root, [string] $Compiled, [string] $Option) {
    & $lean -j1 $Option "--root=$Root" -o $Compiled $Source
    $status = $LASTEXITCODE
    "exit=$status"
    if ($status -ne 0) { throw "Lean failed for $Source" }
}

$savedPath = $env:LEAN_PATH
$savedThreads = $env:LEAN_NUM_THREADS
try {
    $env:LEAN_PATH = (@($out, $upstream, $quartic) + $libraries) -join [IO.Path]::PathSeparator
    $env:LEAN_NUM_THREADS = '1'
    foreach ($name in @('StCircleArgumentPrinciple', 'PCircleArgumentPrinciple')) {
        $module = "$group/$name"
        $object = & git -C $checkout rev-parse "$($pin):src/$module.lean"
        if ($LASTEXITCODE -ne 0 -or $object -notmatch '^[a-f0-9]{40}$') {
            throw "Missing exact upstream source for $module."
        }
        $source = "$upstream/$module.lean"
        & git -C $checkout cat-file blob $object > $source
        if ($LASTEXITCODE -ne 0) { throw "Could not stage $module." }
        $staged = & git -c core.longpaths=true hash-object --no-filters -- $source
        if ($LASTEXITCODE -ne 0 -or $staged -ne $object) { throw "Upstream source mismatch for $module." }
        "$module $staged"
        Invoke-LeanBuild $source $upstream "$upstream/$module.olean" '-Dlinter.style.haveILetI=false'
    }
    foreach ($module in @('WeightedContourTransfer', 'QuarticContourError')) {
        $module
        Invoke-LeanBuild "$packet/$module.lean" $packet "$out/$module.olean" '-DwarningAsError=true'
    }
}
finally {
    $env:LEAN_PATH = $savedPath
    $env:LEAN_NUM_THREADS = $savedThreads
}
