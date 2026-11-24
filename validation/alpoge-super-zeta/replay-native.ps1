param(
    [Parameter(Mandatory)] [string] $LeanExecutable,
    [Parameter(Mandatory)] [string] $SuperZetaLibrary,
    [Parameter(Mandatory)] [string] $MathlibPackages,
    [string] $OutputDirectory
)

$ErrorActionPreference = 'Stop'
$packet = $PSScriptRoot
$lean = (Resolve-Path -LiteralPath $LeanExecutable).Path
$lib = (Resolve-Path -LiteralPath $SuperZetaLibrary).Path
$packages = Get-ChildItem -Directory -LiteralPath $MathlibPackages |
    ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' } |
    Where-Object { Test-Path -LiteralPath $_ }

$version = & $lean --version
if ($LASTEXITCODE -ne 0 -or $version -notmatch 'version 4\.19\.0,.*6caaee842e94') {
    throw "Use the pinned Lean 4.19.0 binary. Found $version"
}
$version

if (!$OutputDirectory) {
    $OutputDirectory = Join-Path ([IO.Path]::GetTempPath()) "native-dottie-$([Guid]::NewGuid())"
}
$out = (New-Item -ItemType Directory -Path $OutputDirectory -Force).FullName
$previousLakePath = $env:LEAN_PATH
$previousThreads = $env:LEAN_NUM_THREADS
try {
    $env:LEAN_PATH = (@($out, $lib) + $packages) -join [IO.Path]::PathSeparator
    $env:LEAN_NUM_THREADS = '1'
    $modules = @('NativeDottieRay', 'NativeDottieMellin', 'NativeDottieContact', 'NativeDottieOrigin',
        'NativeDottieContour', 'NativeDottieGapDisk')
    foreach ($module in $modules) {
        $module
        & $lean -j1 '-DwarningAsError=true' "--root=$packet" -o "$out/$module.olean" "$packet/$module.lean"
        $status = $LASTEXITCODE
        "exit=$status"
        if ($status -ne 0) {
            throw "Lean failed for $module"
        }
    }
}
finally {
    $env:LEAN_PATH = $previousLakePath
    $env:LEAN_NUM_THREADS = $previousThreads
}

