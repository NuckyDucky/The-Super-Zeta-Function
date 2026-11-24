param(
    [Parameter(Mandatory)] [string] $LeanExecutable,
    [Parameter(Mandatory)] [string] $SuperZetaLibrary,
    [Parameter(Mandatory)] [string] $MathlibPackages,
    [Parameter(Mandatory)] [string] $NativeBuildDirectory,
    [string] $PythonExecutable = 'python',
    [string] $OutputDirectory,
    [switch] $CheckFixedSamples
)

$ErrorActionPreference = 'Stop'
$packet = $PSScriptRoot
$lean = (Resolve-Path -LiteralPath $LeanExecutable).Path
$library = (Resolve-Path -LiteralPath $SuperZetaLibrary).Path
$native = (Resolve-Path -LiteralPath $NativeBuildDirectory).Path
$packages = Get-ChildItem -Directory -LiteralPath $MathlibPackages |
    ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' } |
    Where-Object { Test-Path -LiteralPath $_ }
if (!(Test-Path -LiteralPath (Join-Path $native 'MellinRationalSum.olean'))) {
    throw 'Build the native packet with replay-native.ps1 before the integer replay.'
}
$version = & $lean --version
if ($LASTEXITCODE -ne 0 -or $version -notmatch 'version 4\.19\.0,.*6caaee842e94') {
    throw "Use the pinned Lean 4.19.0 binary. Found $version"
}
if (!$OutputDirectory) {
    $OutputDirectory = Join-Path ([IO.Path]::GetTempPath()) "native-mellin-integer-$([Guid]::NewGuid())"
}
$out = (New-Item -ItemType Directory -Path $OutputDirectory -Force).FullName
$audit = Join-Path $out 'lean-audit.txt'
$version | Tee-Object -FilePath $audit
& $PythonExecutable -B "$packet/generate_mellin_integer_certificate.py" $out |
    Tee-Object -FilePath (Join-Path $out 'generated-digests.txt')
if ($LASTEXITCODE -ne 0) { throw 'Sample generation failed.' }

function Build-LeanModule([string] $name, [string] $sourceRoot) {
    $name | Tee-Object -FilePath $audit -Append
    & $lean -j1 '-DwarningAsError=true' "--root=$sourceRoot" -o "$out/$name.olean" "$sourceRoot/$name.lean" 2>&1 |
        Tee-Object -FilePath $audit -Append
    $status = $LASTEXITCODE
    "exit=$status" | Tee-Object -FilePath $audit -Append
    if ($status -ne 0) { throw "Lean failed for $name" }
}

$previousLeanPath = $env:LEAN_PATH
$previousThreads = $env:LEAN_NUM_THREADS
try {
    $env:LEAN_NUM_THREADS = '1'
    $env:LEAN_PATH = $out
    Build-LeanModule 'MellinIntegerArithmetic' $packet
    for ($block = 0; $block -lt 37; $block++) {
        Build-LeanModule ('MellinIntegerBlock{0:00}' -f $block) $out
    }
    Build-LeanModule 'MellinIntegerTable' $out
    if ($CheckFixedSamples) {
        Build-LeanModule 'MellinFixedInterval' $packet
        Build-LeanModule 'MellinFixedFunctions' $packet
        Build-LeanModule 'MellinFixedTable' $packet
        Build-LeanModule 'MellinFixedRanges' $packet
    }
    $env:LEAN_PATH = (@($out, $native, $library) + $packages) -join [IO.Path]::PathSeparator
    Build-LeanModule 'MellinIntegerMoment' $packet
    Build-LeanModule 'MellinOuterSamples' $packet
    Build-LeanModule 'MellinIntegerCertificate' $packet
    if ($CheckFixedSamples) {
        Build-LeanModule 'MellinFixedIntervalSound' $packet
        Build-LeanModule 'MellinFixedElementary' $packet
        Build-LeanModule 'MellinFixedLog' $packet
        Build-LeanModule 'MellinFixedDensity' $packet
        Build-LeanModule 'MellinFixedTableSound' $packet
        Build-LeanModule 'MellinFixedAssembly' $packet
    }
}
finally {
    $env:LEAN_PATH = $previousLeanPath
    $env:LEAN_NUM_THREADS = $previousThreads
}
"Audit at $audit"
