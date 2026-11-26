#Requires -Version 7.4
param(
    [Parameter(Mandatory)] [string] $LeanExecutable,
    [Parameter(Mandatory)] [string[]] $SuperZetaLibrary,
    [Parameter(Mandatory)] [string] $MathlibPackages,
    [string[]] $BridgeLibrary = @((Split-Path -Parent $PSScriptRoot)),
    [string] $AlpogeLibrary = (Join-Path (Split-Path -Parent $PSScriptRoot) 'upstream'),
    [string] $OutputDirectory,
    [string] $AlpogeGrowthCheckout
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
    'GaussianCommonDivisorMoebius',
    'GaussianIndexRamp',
    'GaussianIndexWeights',
    'GaussianIndexMoebiusWeights',
    'GaussianPrimitiveIndexWindow',
    'GaussianPrimitiveIndexMellin',
    'GaussianIndexedCutoff',
    'GaussianIndexFamily',
    'GaussianDivisorWindow',
    'GaussianRawWindowCounts',
    'GaussianRawWindowRounding',
    'GaussianRawWindowCriterion',
    'GaussianHalfWindowMultiplicity',
    'GaussianHalfWindowShift',
    'GaussianCenteredHalfWindowShift',
    'GaussianRawPrimeWindow',
    'GaussianRealQuadraticWeights',
    'GaussianFrobeniusFixedMinor',
    'GaussianFrobeniusJetScaffold',
    'GaussianFrobeniusJetMinors',
    'GaussianFrobeniusOrdinaryJet',
    'GaussianSquaredRamp',
    'GaussianDivisorSquaredWindow',
    'GaussianFrobeniusTriangle',
    'SpectralThermometer',
    'GaussianPrimePrefix',
    'GaussianSquaredSmoothing',
    'GaussianPrimeSquaredWindow',
    'ArchivedGaussianTriangleWindow',
    'GaussianTriangleScopeAudit',
    'GaussianLogCutTriangleWindow',
    'GaussianSqrtTriangleWindow',
    'GaussianFrobeniusFactorial',
    'GaussianSqrtFrobeniusBudget',
    'GaussianFrobeniusJetSeparation',
    'GaussianFrobeniusMinorIdeal',
    'GaussianD4MinorSupport',
    'GaussianFrobeniusIdentityMinor',
    'GaussianFrobeniusMinorPowers',
    'GaussianFrobeniusIdentityIdeal',
    'GaussianFrobeniusCentralIdeal',
    'GaussianD4MinorExponents',
    'GaussianQuarticClosure',
    'GaussianQuarticD4',
    'ArchivedGaussianRetainedNormWindow',
    'GaussianClosureUnramified',
    'GaussianClosureFrobenius',
    'GaussianClosurePrimeTrace',
    'ArchivedGaussianNormCriterion',
    'GaussianSquaredRoundingResidual',
    'ArchivedGaussianNormPowerBound',
    'GaussianPrimePrefixKernel',
    'GaussianLocalPrimeWindow',
    'GaussianFifthPowerPrimeWindow',
    'GaussianAveragedRoundingResidual',
    'GaussianCutoffAverageMellin',
    'GaussianAveragedPrimeWindow',
    'GaussianThreeHalvesPrimeWindow',
    'GaussianDyadicPrimeWindow',
    'GaussianDyadicFrobeniusWindow',
    'GaussianHermitePrimePolynomial',
    'GaussianHermiteFrobeniusIdeal',
    'ArchivedGaussianHermiteNorm',
    'GaussianHermiteCoefficientBound',
    'GaussianSeventhFreeEuler',
    'GaussianSeventhFreeMellin',
    'GaussianMoebiusContent',
    'GaussianBalancedMoebius',
    'GaussianMoebiusCommonDivisor',
    'GaussianMoebiusPairContent',
    'GaussianPrimitiveOneCutoff',
    'GaussianPrimeMesh',
    'GaussianPrimeCenter',
    'GaussianPrimeCenterWindow',
    'GaussianVaughanWindow',
    'GaussianVaughanLargestPrime',
    'GaussianVaughanLogWindow',
    'GaussianVaughanWindowCriterion',
    'GaussianVaughanKernelBounds',
    'GaussianVaughanMellinSeries',
    'GaussianVaughanConvolvedKernel',
    'GaussianVaughanPrimeComplement',
    'GaussianVaughanPrimePowers',
    'GaussianVaughanRationalSquares',
    'GaussianVaughanFilteredDirichlet',
    'GaussianVaughanHigherContinuation',
    'GaussianLogDerivativeDisk',
    'GaussianVaughanGammaStrip',
    'GaussianVaughanGaussianStrip',
    'MellinContourShift',
    'GaussianVaughanCofactorBound',
    'GaussianVaughanContourMoments',
    'GaussianVaughanKernelEndpoints'
)

if ($AlpogeGrowthCheckout) {
    $growthRepo = (Resolve-Path -LiteralPath $AlpogeGrowthCheckout).Path
    $growthPin = 'ba2a065656ec7c638baa601994de3e0245ff6665'
    $growthRevision = & git -C $growthRepo rev-parse HEAD
    if ($LASTEXITCODE -ne 0 -or $growthRevision -ne $growthPin) {
        throw "Use the Alpöge source checkout at $growthPin for the growth estimates."
    }
    $growthModules = @(
        'Formalism.LandauZeroFreeBounds.Statement',
        'Formalism.Statement',
        'Formalism.StatementOC',
        'Formalism.ZeroFreeRegion.Statement',
        'Formalism.LandauZeroFreeBounds.NoZeroComplexOf',
        'Formalism.StatementU',
        'Formalism.ZetaNonvanishingGeneralWeights',
        'Formalism.ZetaNonvanishingChebyshevWeights',
        'Formalism.StatementFL',
        'Formalism.LFunctionBounds.Statement',
        'Formalism.LFunctionBounds.PositivityBound',
        'Formalism.LFunctionBounds.LFunctionBoundsProofs.LFunctionEqGOfOneLt',
        'Formalism.LFunctionBounds.LFunctionBoundsProofs.LPartialSum',
        'Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth',
        'Formalism.ZeroFreeRegion.SmallHeightLogDeriv',
        'Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormCpowSubLePoint',
        'Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.DzDifferentiableOn',
        'Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RiemannZetaOneEqOneSubOfRePos',
        'Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth',
        'Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound',
        'Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormLogDerivLeLamF',
        'Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRight',
        'Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight',
        'Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthGamma'
    )
    $growthFiles = @($growthModules | ForEach-Object { 'src/' + $_.Replace('.', '/') + '.lean' })
    & git -C $growthRepo diff --quiet HEAD -- @growthFiles
    if ($LASTEXITCODE -ne 0) { throw 'The pinned Alpöge source files must be unmodified.' }
    $growthBuild = (New-Item -ItemType Directory -Force -Path (Join-Path $out 'growth')).FullName
    $growthSource = Join-Path $growthRepo 'src'
    $modules += @(
        'GaussianDirichletVerticalGrowth',
        'GaussianVaughanFilteredGrowth',
        'GaussianVaughanContourDecay',
        'GaussianVaughanPrimeInversion',
        'GaussianVaughanCompletedPrimeBound',
        'GaussianVaughanLeftLineGamma',
        'GaussianVaughanConvolvedLeftLine',
        'GaussianVaughanSelectedContour',
        'GaussianVaughanGammaFixedStrip',
        'GaussianVaughanGammaRatioStrip',
        'GaussianVaughanConvolvedStrip',
        'GaussianVaughanKernelAtZero',
        'GaussianVaughanBelowWindowBound',
        'GaussianVaughanHigherKernel',
        'GaussianVaughanUpperIdentity',
        'GaussianVaughanUpperShortPrime',
        'GaussianVaughanUpperCofactor',
        'GaussianVaughanUpperError',
        'GaussianVaughanPrimeBand',
        'GaussianVaughanNegativeWindow',
        'GaussianVaughanInertExcess',
        'GaussianVaughanReflectionDescent',
        'GaussianVaughanDetectedPoles',
        'GaussianVaughanBoundaryFree',
        'GaussianVaughanRationalSplit',
        'GaussianVaughanRationalMainTerm',
        'GaussianVaughanCentralExcess',
        'GaussianShortPerron',
        'GaussianShortPerronBounds',
        'GaussianSharpRationalMainTerm',
        'GaussianSharpRationalPrefix',
        'GaussianDyadicCentralPrimeCriterion',
        'GaussianHermiteOddValue',
        'GaussianHermiteSharpCount',
        'GaussianHermiteResidueLattice',
        'GaussianHermiteIntegratedWindow'
    )
}

$savedPath = $env:LEAN_PATH
$savedThreads = $env:LEAN_NUM_THREADS
try {
    $env:LEAN_PATH = (@($out, $upstream) + $bridge + $quartic + $libraries) -join
        [IO.Path]::PathSeparator
    $env:LEAN_NUM_THREADS = '1'
    if ($AlpogeGrowthCheckout) {
        $importFiles = Get-ChildItem -LiteralPath $upstream -Recurse -File |
            Where-Object { $_.Name -match '\.(?:olean(?:\.(?:private|server))?|ir)$' }
        foreach ($file in $importFiles) {
            $relative = [IO.Path]::GetRelativePath($upstream, $file.FullName)
            $staged = Join-Path $growthBuild $relative
            if (Test-Path -LiteralPath $staged) {
                if ((Get-FileHash -Algorithm SHA256 -LiteralPath $file.FullName).Hash -ne
                    (Get-FileHash -Algorithm SHA256 -LiteralPath $staged).Hash) {
                    throw "Incompatible Alpöge import in $relative."
                }
                continue
            }
            $null = New-Item -ItemType Directory -Force -Path (Split-Path -Parent $staged)
            Copy-Item -LiteralPath $file.FullName -Destination $staged
        }
        $env:LEAN_PATH = $growthBuild + [IO.Path]::PathSeparator + $env:LEAN_PATH
        "Alpöge growth source $growthRevision"
        foreach ($module in $growthModules) {
            $relative = $module.Replace('.', '/')
            $compiled = Join-Path $growthBuild "$relative.olean"
            $null = New-Item -ItemType Directory -Force -Path (Split-Path -Parent $compiled)
            $module
            & $lean -j1 "--root=$growthSource" -o $compiled (Join-Path $growthSource "$relative.lean")
            $status = $LASTEXITCODE
            "exit=$status"
            if ($status -ne 0) { throw "Lean failed for $module." }
        }
    }
    foreach ($module in $modules) {
        $module
        $leanArgs = @('-j1', '-DwarningAsError=true', "--root=$PSScriptRoot")
        if ($module -in @('GaussianVaughanGaussianStrip', 'GaussianDirichletVerticalGrowth',
                'GaussianVaughanFilteredGrowth', 'GaussianVaughanContourDecay', 'MellinContourShift',
                'GaussianVaughanCofactorBound', 'GaussianVaughanPrimeInversion',
                'GaussianVaughanCompletedPrimeBound', 'GaussianVaughanLeftLineGamma',
                'GaussianVaughanContourMoments', 'GaussianVaughanConvolvedLeftLine',
                'GaussianVaughanSelectedContour', 'GaussianVaughanGammaFixedStrip',
                'GaussianVaughanGammaRatioStrip', 'GaussianVaughanConvolvedStrip',
                'GaussianVaughanKernelAtZero', 'GaussianVaughanBelowWindowBound',
                'GaussianVaughanKernelEndpoints', 'GaussianVaughanHigherKernel',
                'GaussianVaughanUpperIdentity', 'GaussianVaughanUpperShortPrime',
                'GaussianVaughanUpperCofactor', 'GaussianVaughanUpperError',
                'GaussianVaughanPrimeBand', 'GaussianVaughanNegativeWindow',
                'GaussianVaughanInertExcess', 'GaussianVaughanReflectionDescent',
                'GaussianVaughanDetectedPoles', 'GaussianVaughanBoundaryFree',
                'GaussianVaughanRationalSplit', 'GaussianVaughanRationalMainTerm',
                'GaussianVaughanCentralExcess', 'GaussianShortPerron', 'GaussianShortPerronBounds',
                'GaussianSharpRationalMainTerm', 'GaussianSharpRationalPrefix', 'GaussianDyadicCentralPrimeCriterion',
                'GaussianHermiteOddValue', 'GaussianHermiteSharpCount', 'GaussianHermiteResidueLattice',
                'GaussianHermiteIntegratedWindow')) {
            $leanArgs += '-M4000'
        }
        & $lean @leanArgs -o "$out/$module.olean" "$PSScriptRoot/$module.lean"
        $status = $LASTEXITCODE
        "exit=$status"
        if ($status -ne 0) { throw "Lean failed for $module." }
    }
}
finally {
    $env:LEAN_PATH = $savedPath
    $env:LEAN_NUM_THREADS = $savedThreads
}
