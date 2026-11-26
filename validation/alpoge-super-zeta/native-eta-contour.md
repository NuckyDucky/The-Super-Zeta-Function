# The first Dottie contour from finite eta data

I keep the original disk with center $c=1/4+7.067363i$ and radius $1/4096$. I read the count and location on the ordered Dottie cross-product $C=J_-Z_+-J_+Z_-$. Put $W=J_--J_+$, $A(s)=\pi^{-2s}(3^{2s}-1)$, and $B(s)=1-2^{1-2s}$. In the open spectral strip,

$$
H(s)=B(s)\zeta(2s),\qquad C(s)=\frac{W(s)A(s)}{B(s)}H(s).
$$

If the Mellin replay proves $W$ nonzero on the disk and $H$ has one simple zero $\rho$ there, Lean transfers the same simple zero to $C$. If $p$ is entire, Lean reads $p(\rho)$ from the weighted circle of $C$. Weight $1$ gives the count and weight $s-c$ gives the displacement. [Lean transfer](NativeDottieEtaContour.lean)

## From the Mellin integral to the finite sum

For the ordinary eta function, Lean checks the Fermi kernel identity on $\Re w>0,\ \Im w>0$. With $q=(1-e^{-x})/2$ on the positive ray, the geometric expansion of $e^{-x}/(1+e^{-x})$ leaves a factor $q^N$. Its Mellin integral gives an absolute error of at most $2^{-N}\Gamma(\Re w)/|\Gamma(w)|$ for the normalized sum. [Mellin identity](EtaMellin.lean) · [Remainder](EtaEulerRemainder.lean) · [Finite sum](EtaEulerSum.lean)

On the spectral scale I use

$$
P(s)=\sum_{k=0}^{127}\frac{1}{2^{k+1}}\sum_{j=0}^{k}(-1)^j\binom{k}{j}(j+1)^{-2s}.
$$

Lean collects this into 128 powers of $(j+1)^{-2s}$. The coefficient at index $j$ is $(-1)^j$ times $1-2^{-128}\sum_{m=0}^{j}\binom{128}{m}$. I use one binomial row for all the weights. [Column identity](EtaEulerColumns.lean)

Lean proves $|H-P|\le 10^{-14}$ on $|s-c|\le 1/32$. It uses Gamma reflection for this bound and the Cauchy derivative estimate to get $|H'-P'|\le 10^{-12}$ on the original disk. Lean bounds the variation of $P'$ there by $2304/4096$. [Gamma bounds](EtaGammaBound.lean) · [Uniform errors](EtaEulerDisk.lean) · [Derivative variation](EtaEulerContourBounds.lean)

## The kernel certificate for the center and the disk

The 128 columns give separate enclosures for the real and imaginary parts of $P(c)$ and $P'(c)$. I evaluate the logarithm, exponential, and phase with outward-rounded integer intervals. Lean checks the finite comparison by `decide +kernel`. Its Boolean theorem has no axiom dependencies.

The soundness proof gives $\lvert P(c)\rvert\le 3\cdot10^{-6}$ and $\lvert P'(c)-(15/4-i/4)\rvert\le 1/20$. The estimates above then give the eta residual bound $10^{-6}$ and relative derivative bound $1/4$ on the disk. [Integer comparison](EtaCenterFixed.lean) · [Basis enclosures](EtaCenterBasisSound.lean) · [Exact complex bounds](EtaCenterCertificate.lean)

Lean proves that $|W(s)|>11600$ throughout the closed disk. The original cross-product has exactly one simple zero $\rho$ in that disk, with $\Re \rho=1/4$ and $|\rho-c|\le 4/(3\cdot10^6)$. Its weighted circle reads $p(\rho)$ for every entire $p$. In particular the count is $1$ and the weighted address is exactly $\rho$. [Closed disk certificate](FirstDottieCrossCertificate.lean) · [Lean 4.19.0 build and axioms](native-dottie-cross-audit.txt)

To replay the eta modules, set `LEAN_PATH` to the integer and native replay output directories followed by the pinned Super Zeta and Mathlib library directories from the [integer replay](native-mellin-quadrature.md#the-weighted-sums-reduce-in-the-kernel). With the packet as the current directory, compile these modules in order. Put the generated objects in the integer replay directory.

```powershell
$packet = (Get-Location).Path
$modules = @('NativeDottieEtaContour', 'EtaMellin', 'EtaEulerRemainder',
    'EtaGammaBound', 'EtaEulerSum', 'EtaEulerColumns', 'EtaEulerDisk', 'EtaEulerContourBounds',
    'EtaCenterFixed', 'EtaCenterBasisSound', 'EtaCenterCertificate', 'EtaFirstDisk')
foreach ($module in $modules) {
    & $lean419 -j1 '-DwarningAsError=true' "--root=$packet" `
        -o "$integerOutput/$module.olean" "$packet/$module.lean"
    if ($LASTEXITCODE -ne 0) { throw "Lean failed for $module" }
}
```

Run the [full middle replay](native-mellin-quadrature.md#checking-the-middle-samples-in-lean) to build `MellinMiddleAll.olean`. Add `$integerOutput/middle-batches` to the same `LEAN_PATH` and run the closed certificate.

~~~powershell
$middleOutput = Join-Path $integerOutput 'middle-batches'
$env:LEAN_PATH = (@($middleOutput, $env:LEAN_PATH) -join [IO.Path]::PathSeparator)
& $lean419 -j1 '-DwarningAsError=true' "--root=$packet" `
    -o "$integerOutput/FirstDottieCrossCertificate.olean" "$packet/FirstDottieCrossCertificate.lean"
if ($LASTEXITCODE -ne 0) { throw "Lean failed for FirstDottieCrossCertificate" }
~~~
