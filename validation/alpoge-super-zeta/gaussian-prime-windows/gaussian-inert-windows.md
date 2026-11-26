# An upper bound on inert Gaussian primes

For the original quartic let $k=\mathbb Q(i)$, $D=26509772707289$, and
$K=k(\sqrt{-5045155+1027708i})$. Write $G$ for the Gaussian factor of
$\zeta_K=\zeta\,\beta\,G$ and $W_1(x)$ for the corrected prime-only ramp.

## Why the lower bound on $W_1$ works

- If $x\ge0$, the checked prefix sums give $K_{\theta}(x)>0$ for the centered
  theta kernel. Theta reflection makes it even. Folding the Mellin integral
  gives the real-axis reading
  \[
  \Lambda_G(\sigma)=2\int_0^\infty K_{\theta}(x)
      \cosh\bigl((\sigma-\tfrac12)x\bigr)\,dx>0
  \]
  for every real $\sigma$. The tail estimate in Lean proves integrability
  even for an arbitrarily large real Mellin exponent. [Prefix certificate](../../../verification/quartic-kernel/source/QuarticCheckedShellKernel.lean) · [Real-axis proof](QuarticPositiveReal.lean)
- At $\Re w>0$, the completion factors are nonzero. The Gaussian zeros in
  that half-plane therefore have nonzero imaginary part. Reversing the sign
  of the ramp reverses each pole residue without moving any pole. The
  positivity condition in Alpöge's window theorem is only imposed at real
  poles, so it is satisfied for the reversed ramp.
- If $-W_1(x)\le Cx^\theta$ through arbitrarily late windows
  $[Y,Y^{1+\delta}]$ for each $1/2<\theta<1$, then the previous higher-power
  estimate gives the corresponding bound for the reversed full ramp.
  This excludes the upper-right Gaussian zeros. The field theorem uses
  reflection and the rational Dirichlet cofactor result to obtain
  `DedekindZetaRH QuarticModel.K`. [Lean window implication](GaussianLowerPrimeWindow.lean)

The Lean 4.19.0 proof gives positivity of the explicit quartic Mellin formula
for every real $\sigma$. Lean 4.33.1 identifies that same formula with the
field library's archived Mellin transform. The latter replay takes that
positivity statement as the explicit argument `hpos`. The two printed
audits show the kernel checks in their pinned toolchains. [Shared formula](QuarticRealFormula.lean) · [4.19.0 audit](quartic-real-positivity-audit.txt) · [4.33.1 audit](replay-audit.txt)

## Which positive count to bound

Let $a(p)$ be the original Gaussian Euler weight at a rational prime $p$.
Let $U(p)$ count the degree-one Gaussian primes above $p$ with a nonzero
relative character, and $I(p)$ count those with relative character $-1$.
A split prime contributes $+1$, an inert prime contributes $-1$, and
a ramified prime contributes $0$. This gives the exact Lean identity
\[
a(p)=U(p)-2I(p).
\]
For $p\nmid 2D$, $U(p)=1+\chi_{-4}(p)$. At $p=5,73,13$, respectively,
the checked signed weights are $2,0,-2$. The corresponding inert counts
are $0,1,2$. [Lean prime count identities](GaussianInertPrimeWeights.lean)

For $x\ge1$, write
\[
\begin{aligned}
\Theta_U(t)&=\sum_{\substack{p\le t\\p\nmid2D}}U(p)\log p,&
\Theta_I(t)&=\sum_{\substack{p\le t\\p\nmid2D}}I(p)\log p,\\
R_U(x)&=-\int_x^\infty\frac{\Theta_U(t)-t}{t^2}\,dt,&
R_I(x)&=-\int_x^\infty\frac{\Theta_I(t)-t/2}{t^2}\,dt .
\end{aligned}
\]
With $d_I=\int_1^\infty(\Theta_I(t)-t/2)t^{-2}\,dt$, partial
summation gives the same normalized cutoff as in the rational proof.
\[
R_I(x)=\sum_{\substack{p\le x\\p\nmid2D}}I(p)\log p
      \left(\frac1p-\frac1x\right)-\tfrac12\log x-d_I .
\]
The centered formula for $E_G(x)=W_1(x)/x$ from the earlier
prime-class calculation gives, once $x$ exceeds the finitely many
exceptional primes,
\[
E_G(x)=R_U(x)-2R_I(x)-\frac1x\sum_{p\mid2D}a(p)\log p .
\]
Indeed, the prime sum for $E_G$ contains $\Theta_U-2\Theta_I$ away from
$2D$, and the two linear main terms cancel. The rational Dirichlet result
gives $\Theta_U(t)=t+O(\sqrt t\log^2t)$ and hence
$R_U(x)=O(x^{-1/2}\log^2x)$. The integrals converge unconditionally for this
fixed field by effective Chebotarev and the earlier centering argument.
Thus
\[
-E_G(x)=2R_I(x)+O(x^{-1/2}\log^2x).
\]
Counting Gaussian primes of degree two as well changes $R_I(x)$ by
$O(x^{-1/2}\log x)$, after adjusting its centering constant. Their norms are
$p^2$ and their cumulative log weight is $O(\sqrt t\log t)$.
[Centering and Chebotarev derivation](gaussian-prime-classes.md) · [Effective Chebotarev, Theorems 1.1 and 1.3](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf#page=3)

If I bound the centered **inert** Gaussian prime count $R_I(x)$ above by
$Cx^{\theta-1}$ throughout the cofinal windows, I get the required lower
bound for $W_1$ with the same exponent and window width. This is the same
direction as Sernau's upper bound for the positive non-split weights
$\Lambda(n)(1-(n/d))$ over rational primes. The input to establish is that
estimate for the relative character on the prime ideals of $\mathbb Q(i)$.
The two Lean files check the prime coefficients and the lower-bound
implication. The centered estimate and its comparison above use classical
prime counting. [Sernau’s positive weights](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/PrimeError.lean#L23) · [Sernau’s upper bound](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Main.lean#L149)

In `Data.primeSum`, the same rational integer $\nu$ gives both the size
in the cutoff and the residue class in `placeOfInt`. For the Gaussian
count, the size is the ideal norm and the sign uses the marked ideal.
Lean already writes the character on a Gaussian generator $a+bi$ as the
Jacobi symbol of $-5045155a+1027708b$ modulo $D$. The two generators of
norm $73$ show which information that step must retain. [Sernau’s prime sum and place selection](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/AdmissibleData.lean#L136) · [Gaussian coordinate formula](../../../lean-ideal73/RelativeQuarticSplitSign.lean#L46)
