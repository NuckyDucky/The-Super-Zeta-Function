# Signed prime bounds on $[Y,Y^{3/2}]$

I average the squared cutoff once. If the signed prime prefixes have an upper bound of $B n^{7/8}$ everywhere and an upper bound of $A_\theta n^\theta$ throughout arbitrarily late $[Y,Y^{3/2}]$, the averaged cutoff has the required one-sided bound throughout $[Y^{5/4},Y^{3/2}]$. If the local estimate holds for each $1/2<\theta\le3/4$, Lean gives Dedekind RH for the actual quartic with the rational Dirichlet and real-axis positivity inputs. [Exact theorem and premises](GaussianThreeHalvesPrimeWindow.lean) · [Source replay and axioms](gaussian-averaged-prime-window-audit.txt)

## Why the earlier primes fit

Write $A(x)$ for the centered prime squared cutoff, $c$ for the archived center, $b(p)$ for the signed prime coefficient, and $P(n)=\sum_{p\le n}(-b(p))$. If $R$ is the squared rounding residual, define

$$
T(y)=\frac2y\int_0^y R(t)\,dt-R(y),\qquad
\mathcal F[A](x)=\frac2x\int_1^x A(t)\,dt-A(x).
$$

The lower limit at $1$ gives the exact finite identity

$$
\mathcal F[A](x)=\sum_{p\le x}(-b(p))T(x/p)+\frac{c}{3x}\qquad(x\ge1).
$$

Lean checks that $T$ is increasing, is zero on $[0,1]$, and lies between $0$ and $1/2$. If I sum by parts, the weight on each prefix $P(n)$ is nonnegative and at most $(1+(2/3)\log x)/x$. The total weight is at most $1/2$. The center enters only through $c/(3x)$. [Residual estimates](GaussianAveragedRoundingResidual.lean) · [Finite sum and prefix bound](GaussianAveragedPrimeWindow.lean)

If $Y^{5/4}\le x\le Y^{3/2}$, the prefixes from $Y$ to $x$ contribute at most $A_\theta x^\theta/2$. The older prefixes contribute at most $B Y^{15/8}(1+(2/3)\log x)/x$. Since $Y^{15/8}\le x^{3/2}$, that is at most $B x^{1/2}(1+(2/3)\log x)$. This fits an $x^\theta$ bound for each $\theta>1/2$. Writing $X=Y^{5/4}$ gives the output window $[X,X^{6/5}]$. [Lean window transfer](GaussianThreeHalvesPrimeWindow.lean)

## Why the pole test still works

If I apply the same average to the original squared cutoff, its Mellin transform is multiplied by $(1-w)/(1+w)$. On $\operatorname{Re}w>1/2$ that factor vanishes only at $w=1$. Real-axis positivity of the completed Gaussian factor excludes a zero there, so the detector retains all the Gaussian poles it tests. The error from replacing the original squared cutoff by its prime contribution remains bounded by a constant times $x^\theta$ after averaging. [Lean Mellin identity and pole test](GaussianCutoffAverageMellin.lean) · [Lean error transfer](GaussianThreeHalvesPrimeWindow.lean)

## The arithmetic still to supply

The actual signed prefix is twice the difference between the log-weighted counts in the identity and central-involution Frobenius classes of the quartic's splitting field, up to the finite exceptional-prime correction. The fixed zero-free exponent for that splitting field gives the $7/8$ input by the written Chebotarev argument. The local premise asks for one constant $A_\theta$ per exponent that works at every integer in arbitrarily late windows. [Arithmetic Frobenius coefficient](GaussianClosurePrimeTrace.lean) · [Fixed-exponent estimate](gaussian-norm-power-bound.md)

There is also a route back to the original retained-norm cutoff. For the dihedral closure $L$ and its maximal abelian subfield $A_{\rm ab}=\mathbb Q(i,\sqrt D)$, the written factorization is $\zeta_L=\zeta_{A_{\rm ab}}G^2$, where $G$ is the Gaussian factor of the quartic. If the quartic conclusion holds and the rational Dirichlet input is supplied, the factorization puts the nontrivial zeros of $\zeta_L$ on the line. Effective Chebotarev and partial summation then give $P(u)=O(\sqrt{u}\log^2 u)$ and control of the reciprocal center. Those estimates feed the original Lean cutoff transfer at each $\theta>1/2$. This return uses the written factorization and Chebotarev argument. [Factorization](gaussian-biquadratic-class-character.md) · [Effective Chebotarev](https://arxiv.org/html/2610.18491v2#Thmtheorem1) · [Lean retained-norm transfer](GaussianFifthPowerPrimeWindow.lean)
