# From local prime-prefix bounds to the quartic's norm windows

If the two central Frobenius classes have a sufficiently small signed imbalance on arbitrarily late intervals $[Y,Y^5]$, I get the original norm-window hypothesis for the quartic. The prime bound on the long interval only needs an upper bound. Its complement uses the global $7/8$ bound already obtained from the zero-free exponent and Chebotarev. [Global analytic estimate and center](gaussian-norm-power-bound.md) · [Lean norm-window theorem](GaussianFifthPowerPrimeWindow.lean)

## The signed prefix keeps its sign in the cutoff

Let $b(n)$ be the archived signed prime weight, with $b(n)=0$ at nonprimes. Let $P(n)=\sum_{p\le n}(-b(p))$. The center $c=\lim_{N\to\infty}\sum_{p\le N}b(p)/p$ uses the ordinary ordering by integer address. With $R$ the squared rounding residual, set $w_x(n)=R(x/n)$ for $n\ge1$ and $w_x(0)=1/2$. If $P(n)=O(n^\eta)$ for $\eta<1$, the endpoint $w_x(N)P(N)$ tends to zero. The exact identity is
$$
A_{\rm sq}(x)=\lim_{N\to\infty}\sum_{0\le n<N}P(n)\,\bigl(w_x(n)-w_x(n+1)\bigr).
$$
The weights are nonnegative. Lean uses an ordered limit at the exact archived center. [Exact identity and weight checks](GaussianPrimePrefixKernel.lean)

On one residual cell $y\in[n,n+1]$, writing $r=y-n$ gives $3y^3R'(y)=n(1-3r(1-r))+r^3\le n+r=y$. Thus for any positive integer address, $w_x(n)-w_x(n+1)\le 1/(3x)$. Once $n\ge x$, the weight difference is exactly $x/(3n(n+1))$. [Residual slope bound](GaussianSquaredRoundingResidual.lean) · [Step estimates](GaussianPrimePrefixKernel.lean)

## The interval that reaches the norm

If $P(n)\le A n^\theta$ on $[Y,Z]$, $|P(n)|\le B n^\eta$ globally, and $1\le Y\le x\le Z$, then
$$
 A_{\rm sq}(x)\le
 A\left(\frac12+\frac{1}{3(1-\theta)}\right)x^\theta
 +\frac{B(Y+1)Y^\eta}{3x}
 +\frac{BxZ^{\eta-1}}{3(1-\eta)}.
$$
The first term pays for the signed estimate inside the window. The second pays for the earlier prefixes and the third for the later ones. The high-address bound uses a telescoping difference of $n^{\eta-1}$. [Lean local bound](GaussianLocalPrimeWindow.lean)

If $\eta=7/8$, $Z=Y^5$, and $1/2<\theta<7/8$, the two outside terms fit within $(10B/3)x^\theta$ for
$$
  Y^{5/4}\le x\le Y^{5/(8(1-\theta))}.
$$
For example, if the prime bound is at $\theta=3/5$, a prime window $[Y,Y^5]$ gives a norm window starting at $Y^{5/4}$ and ending at $Y^{25/16}$. The cutoff exponent is still $3/5$. The same interval can be written $[y,y^{1+\delta}]$ with $y=Y^{5/4}$ and $\delta=1/4$. [Checked interval transfer](GaussianFifthPowerPrimeWindow.lean)

If I can supply those prime windows for every $1/2<\theta\le3/4$, the smaller exponents also supply every larger exponent required by the original cutoff hypothesis. The checked triangle and norm comparisons give the original $h_{\rm cut}$ at the actual quartic. The final quartic theorem takes the ordered center, the global envelope, the cofinal signed prime windows, the Dirichlet zero input, and positivity on the real axis. [Exact theorem](GaussianFifthPowerPrimeWindow.lean) · [Replay and axiom audit](gaussian-local-prime-window-audit.txt)
