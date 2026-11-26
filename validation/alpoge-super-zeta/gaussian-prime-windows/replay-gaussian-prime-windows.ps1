#Requires -Version 7.4
param(
    [Parameter(Mandatory)] [string] $LeanExecutable,
    [Parameter(Mandatory)] [string[]] $SuperZetaLibrary,
    [Parameter(Mandatory)] [string] $MathlibPackages,
    [string[]] $BridgeLibrary = @((Split-Path -Parent $PSScriptRoot)),
    [string] $AlpogeLibrary = (Join-Path (Split-Path -Parent $PSScriptRoot) 'upstream'),
    [string] $OutputDirectory
)

$ErrorActionPreference = 'Stop'
$lean = (Resolve-Path -LiteralPath $LeanExecutable).Path
$quartic = $SuperZetaLibrary | ForEach-Object { (Resolve-Path -LiteralPath $_).Path }
$bridge = $BridgeLibrary | ForEach-Object { (Resolve-Path -LiteralPath $_).Path }
$upstream = (Resolve-Path -LiteralPath $AlpogeLibrary).Path
$packages = (Resolve-Path -LiteralPath $MathlibPackages).Path
$mathlibPin = '0df444a360eaa60ab8c11dca51a86af692955474'

$version = & $lean --version
if ($LASTEXITCODE -ne 0 -or $version -notmatch '819816b2e0a3bf405af45ae5c7af2491d8f5bee6') {
    throw "Use Lean 4.33.1 at the recorded revision. Found $version"
}
$revision = & git -C "$packages/mathlib" rev-parse HEAD
if ($LASTEXITCODE -ne 0 -or $revision -ne $mathlibPin) {
    throw "The Mathlib checkout must be at $mathlibPin."
}
$version
"Mathlib $revision"

if (!$OutputDirectory) {
    $suffix = [Guid]::NewGuid().ToString('N').Substring(0, 12)
    $OutputDirectory = Join-Path ([IO.Path]::GetTempPath()) "gw-$suffix"
}
$out = (New-Item -ItemType Directory -Path $OutputDirectory -Force).FullName
$libraries = Get-ChildItem -Directory -LiteralPath $packages |
    ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' } |
    Where-Object { Test-Path -LiteralPath $_ }
$modules = @(
    'GaussianPrimeRamp',
    'ArchivedGaussianPrimeWeights',
    'ArchivedGaussianEulerDerivative',
    'ArchivedGaussianLogDerivative',
    'GaussianPrimeWindowKnots',
    'GaussianHigherPrimePowers',
    'GaussianPrimeOnlyWindow',
    'GaussianPrimeSupport',
    'GaussianNormOrientation',
    'QuarticRealFormula',
    'GaussianLowerPrimeWindow',
    'GaussianInertPrimeWeights',
    'GaussianConductorResidue',
    'GaussianBiquadraticInertWeights',
    'GaussianRelativeFrobenius',
    'GaussianRelativeDeterminant',
    'GaussianCMPrimeBarrier',
    'GaussianCommonDivisor',
    'GaussianIdealCommonDivisor',
    'GaussianCommonDivisorLift',
    'GaussianCommonDivisorPowers',
    'GaussianCommonDivisorMoebius'
)

$savedPath = $env:LEAN_PATH
$savedThreads = $env:LEAN_NUM_THREADS
try {
    $env:LEAN_PATH = (@($out, $upstream) + $bridge + $quartic + $libraries) -join
        [IO.Path]::PathSeparator
    $env:LEAN_NUM_THREADS = '1'
    foreach ($module in $modules) {
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
