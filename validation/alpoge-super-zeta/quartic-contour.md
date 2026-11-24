# A contour bound for the quartic's signed prime detector

I use the already continued equal-sign prime detector $S$ for the archived Gaussian factor $G$. Its defining relation on the right measuring circle is

$$
2S(w)G(w)=H'(w)G(w)-G'(w),
$$

where the Euler remainder $H$ is holomorphic on $\Re w>1/2$. I keep $w$ on the Riemann scale. The right disk has center $33/64+i(T-1/512)$ and radius $r=31/2048$. Its leftmost real coordinate is $1025/2048$, so the entire closed disk lies in that half-plane. [Archived detector](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/docs/proofs/gaussian-ideals-and-super-zeta.md#which-prime-signs-detect-an-off-line-gaussian-zero) · [Archived disk](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/lean-ideal73/ArchivedQuarticZeroTransport.lean#L97)

If $G$ is nonzero on the circle $\Gamma$, then for any holomorphic weight $p$ the relation above gives

$$
\frac{1}{2\pi i}\oint_\Gamma p(w)\frac{G'(w)}{G(w)}\,dw
=-\frac{1}{\pi i}\oint_\Gamma p(w)S(w)\,dw.
$$

The term $pH'$ has integral zero. If $A$ is holomorphic on a neighborhood of the disk and $|S-A|\le e$ on $\Gamma$, the integral of $A$ is also zero. The weight $p=1$ then gives a bound of $2re$ for the absolute zero count. Alpöge's weighted circle theorem identifies that count with the cardinality of the zero multiset. If $2re<1$, the cardinality is zero. This uses the actual full argument principle from his pinned source. [Weighted detector identity](WeightedContourTransfer.lean) · [Alpöge's weighted circle proof](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCircleArgumentPrinciple.lean) · [Lean count bound](QuarticContourError.lean)

On my archived right disk, the exact threshold is $e<1024/31$. If the detector identity, boundary nonvanishing, and that uniform error hold, Lean clears $G$ on the closed right disk and its same-height mirror. The mirror uses the existing completed Gaussian reflection. The error is for the **continued** equal-sign detector. Taking $A$ to be a finite equal-sign prime sum leaves the uniform approximation to prove on the selected circumference. [Quartic theorem and exact inputs](QuarticContourError.lean) · [Build and axiom audit](quartic-contour-lean-audit.txt)

The 4.33.1 replay stages the two original circle-argument modules directly from the pinned Git objects and compiles my two local modules. Use the built `lean-ideal73` library and the same Mathlib pin as the [main replay](README.md#replay).

~~~powershell
.\replay-quartic-contour.ps1 -AlpogeCheckout $alpogeCheckout -LeanExecutable $leanBinary `
  -QuarticLibrary $superZetaLibrary -MathlibPackages $mathlibPackages
~~~
