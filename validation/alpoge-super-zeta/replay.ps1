param(
    [Parameter(Mandatory)] [string] $LeanExecutable,
    [Parameter(Mandatory)] [string] $SuperZetaLibrary,
    [Parameter(Mandatory)] [string] $MathlibPackages,
    [switch] $ReuseUpstream
)

$ErrorActionPreference = 'Stop'
$packet = $PSScriptRoot
$lean = (Resolve-Path -LiteralPath $LeanExecutable).Path
$projectLibrary = (Resolve-Path -LiteralPath $SuperZetaLibrary).Path
$packages = Get-ChildItem -Directory -LiteralPath $MathlibPackages |
    ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' } |
    Where-Object { Test-Path -LiteralPath $_ }
$env:LEAN_PATH = (@($packet, "$packet/upstream", $projectLibrary) + $packages) -join
    [IO.Path]::PathSeparator
$env:LEAN_NUM_THREADS = '1'

$version = & $lean --version
if ($LASTEXITCODE -ne 0 -or $version -notmatch '819816b2e0a3bf405af45ae5c7af2491d8f5bee6') {
    throw "Use the pinned Lean 4.33.1 binary. Found $version"
}
$version

function Build-Module([string] $root, [string] $module, [string] $options) {
    $source = Join-Path $root "$module.lean"
    $compiled = Join-Path $root "$module.olean"
    if (!(Test-Path -LiteralPath $source)) {
        throw "Missing source $source. Stage upstream modules with trace_upstream.py first."
    }
    $module
    & $lean -j1 $options "--root=$root" -o $compiled $source
    $status = $LASTEXITCODE
    "exit=$status"
    if ($status -ne 0) {
        throw "Lean failed for $module"
    }
}

$order = Get-Content -LiteralPath "$packet/upstream-analytic-order.txt"
foreach ($module in $order) {
    if ($ReuseUpstream -and (Test-Path -LiteralPath "$packet/upstream/$module.olean")) {
        "cached $module"
        continue
    }
    Build-Module "$packet/upstream" $module '-Dlinter.style.haveILetI=false'
}

foreach ($module in @('SpectralBridge', 'AlpogeAdapters', 'GaussianEndpoint',
    'OrdinaryInteractions', 'ContactOrders', 'ResidueGridPort', 'SpectralMellin', 'SignedContact', 'OrderedContact',
    'GaussianPolePort', 'GaussianWindowPort', 'GaussianRealPoles')) {
    Build-Module $packet $module '-DwarningAsError=true'
}
