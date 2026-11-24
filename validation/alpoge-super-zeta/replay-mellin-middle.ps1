param(
    [Parameter(Mandatory)] [string] $LeanExecutable,
    [Parameter(Mandatory)] [string] $IntegerBuildDirectory,
    [string] $OutputDirectory,
    [ValidateRange(0, 431)] [int] $FirstBatch = 0,
    [ValidateRange(1, 432)] [int] $BatchCount = 1
)

$ErrorActionPreference = 'Stop'
$lean = (Resolve-Path -LiteralPath $LeanExecutable).Path
$integer = (Resolve-Path -LiteralPath $IntegerBuildDirectory).Path
$version = & $lean --version
if ($LASTEXITCODE -ne 0 -or $version -notmatch 'version 4\.19\.0,.*6caaee842e94') {
    throw "Use the pinned Lean 4.19.0 binary. Found $version"
}
if ($FirstBatch + $BatchCount -gt 432) { throw 'The middle replay has 432 four-panel batches.' }
if (!$OutputDirectory) { $OutputDirectory = Join-Path $integer 'middle-batches' }
$out = (New-Item -ItemType Directory -Path $OutputDirectory -Force).FullName
$audit = Join-Path $out 'lean-audit.txt'
$fingerprint = Join-Path $out 'inputs.sha256'

$modules = @('MellinFixedInterval', 'MellinFixedFunctions', 'MellinFixedTable',
    'MellinFixedRanges', 'MellinIntegerArithmetic', 'MellinIntegerTable') +
    @(0..36 | ForEach-Object { 'MellinIntegerBlock{0:00}' -f $_ })
$inputs = $modules | ForEach-Object {
    $file = Join-Path $integer "$_.olean"
    if (!(Test-Path -LiteralPath $file -PathType Leaf)) {
        throw "Run replay-mellin-integer.ps1 with -CheckFixedSamples. Missing $_.olean"
    }
    "$_ $((Get-FileHash -LiteralPath $file -Algorithm SHA256).Hash)"
}
if (Test-Path -LiteralPath $fingerprint) {
    if (($inputs -join "`n") -ne ((Get-Content -LiteralPath $fingerprint) -join "`n")) {
        throw 'The integer proof inputs changed. Use a fresh output directory for this replay.'
    }
} else {
    Set-Content -LiteralPath $fingerprint -Value $inputs -Encoding utf8NoBOM
}

function Build-MiddleModule([string] $name) {
    $source = Join-Path $out "$name.lean"
    $object = Join-Path $out "$name.olean"
    $timer = [Diagnostics.Stopwatch]::StartNew()
    & $lean -j1 '-DwarningAsError=true' "--root=$out" -o $object $source 2>&1 |
        Tee-Object -FilePath $audit -Append
    $status = $LASTEXITCODE
    "$name exit=$status ($([math]::Round($timer.Elapsed.TotalSeconds, 2)) s)" |
        Tee-Object -FilePath $audit -Append
    if ($status -ne 0) { throw "Lean failed for $name" }
}

function Test-BatchObject([string] $name) {
    $object = Join-Path $out "$name.olean"
    $stamp = Join-Path $out "$name.sha256"
    if (!(Test-Path -LiteralPath $object -PathType Leaf) -or
        !(Test-Path -LiteralPath $stamp -PathType Leaf)) { return $false }
    return (Get-Content -LiteralPath $stamp -Raw).Trim() -ceq
        (Get-FileHash -LiteralPath $object -Algorithm SHA256).Hash
}

$previousPath = $env:LEAN_PATH
$previousThreads = $env:LEAN_NUM_THREADS
try {
    $env:LEAN_NUM_THREADS = '1'
    $env:LEAN_PATH = (@($out, $integer)) -join [IO.Path]::PathSeparator
    $version | Tee-Object -FilePath $audit -Append
    for ($batch = $FirstBatch; $batch -lt $FirstBatch + $BatchCount; $batch++) {
        $name = 'MellinMiddleBatch{0:000}' -f $batch
        $start = 576 + 4 * $batch
        $source = Join-Path $out "$name.lean"
        $object = Join-Path $out "$name.olean"
        $sourceText = @"
import MellinFixedRanges

namespace DottieOriented.NativeSpectrum.MellinFixed

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
theorem $($name)_checked : checkTableRange $start 4 = true := by
  decide +kernel

#print axioms $($name)_checked

end DottieOriented.NativeSpectrum.MellinFixed
"@
        if ((Test-BatchObject $name) -and
            (Test-Path -LiteralPath $source -PathType Leaf) -and
            ([IO.File]::ReadAllText($source) -ceq $sourceText)) {
            "$name already checked against these inputs" | Tee-Object -FilePath $audit -Append
            continue
        }
        [IO.File]::WriteAllText($source, $sourceText)
        Build-MiddleModule $name
        $stamp = Join-Path $out "$name.sha256"
        (Get-FileHash -LiteralPath $object -Algorithm SHA256).Hash |
            Set-Content -LiteralPath $stamp -Encoding utf8NoBOM
    }
    $batchNames = @(0..431 | ForEach-Object { 'MellinMiddleBatch{0:000}' -f $_ })
    if (@($batchNames | Where-Object { !(Test-BatchObject $_) }).Count -eq 0) {
        $assembly = @($batchNames | ForEach-Object { "import $_" })
        $assembly += '', 'namespace DottieOriented.NativeSpectrum.MellinFixed', ''
        $assembly += 'private theorem through000 : checkTableRange 576 4 = true := MellinMiddleBatch000_checked', ''
        for ($batch = 1; $batch -lt 432; $batch++) {
            $suffix = '{0:000}' -f $batch
            $previous = '{0:000}' -f ($batch - 1)
            $priorCount = 4 * $batch
            $count = 4 * ($batch + 1)
            $assembly += "private theorem through$suffix : checkTableRange 576 $count = true :=",
                "  joinTableRanges 576 $priorCount 4 through$previous MellinMiddleBatch$($suffix)_checked", ''
        }
        $assembly += 'theorem middle_samples_checked : checkTableRange 576 1728 = true := through431',
            '', '#print axioms middle_samples_checked', '', 'end DottieOriented.NativeSpectrum.MellinFixed'
        Set-Content -LiteralPath (Join-Path $out 'MellinMiddleAll.lean') -Value $assembly -Encoding utf8NoBOM
        Build-MiddleModule 'MellinMiddleAll'
    }
}
finally {
    $env:LEAN_PATH = $previousPath
    $env:LEAN_NUM_THREADS = $previousThreads
}
"Audit at $audit"
