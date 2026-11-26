# The completed prime sum and the complementary cutoff

I write $G$ for the Gaussian factor, $B(n)$ for its signed ideal coefficients, $L(n)$ for its signed Mangoldt coefficients, and $M$ for the Mellin transform of the two-scale theta weight $H_D$. If I fold $B(n)$ into that weight, I get the actual cofactor kernel $K_D(v)=\sum_{n\ge1}B(n)H_D(nv)$. Lean checks its Mellin transform $M(z)G(z)$ for $\Re z>1$. The convolution proof keeps the divisor pair $(m,n)$ and the argument $mnv$ together. [Kernel and convolution](GaussianVaughanConvolvedKernel.lean)

If I complete the prime sum at each cofactor, I get $P_D(v)=\sum_p L(p)K_D(pv)$. Write $\Pi(z)$ for the higher-prime-power part of the signed Mangoldt series. On $\Re z>1$ the Mellin transform of $P_D$ is

$$
 M(z)\bigl(-G'(z)-G(z)\Pi(z)\bigr).
$$

If $U$ is analytic on a strip joining the original and new contours and agrees with $M\Pi$ where $\Re z>1$, then $M(-G')-GU$ continues the completed prime transform to that strip. This is where the full Gaussian log derivative clears against $G$. The contour shift still needs the continuation and vertical bounds for $U$. [Prime completion and continuation](GaussianVaughanConvolvedKernel.lean)

## The sign of the discarded terms

I write $F(X)=\sum_{n\ge1}L(n)H_D(n/X)$ for the full signed sum. I take $\ell=\log X$, $V=X/\ell^{5/2}$, and $q=X/\ell^5$. Each cofactor sum uses $1\le m\le\ell^{8/3}$, the real part of the archived inverse coefficient, and the argument $m/X$.

- $T_\uparrow$ uses the prime weight $1-W(p/V)$.
- $C_{\mathrm{prime}}$ uses $P_D$ with the full prime sum.
- $T_{\mathrm{below}}$ uses $W(p/V)$ on $p\le q$ within the finite cutoff $p\le2V$.

If $X>1$ and $W(u)=0$ for $u\ge2$, Lean checks the following identity for the exact lower sum $T_W$ in the quartic theorem.

$$
T_W(X)=T_\uparrow(X)-C_{\mathrm{prime}}(X)+T_{\mathrm{below}}(X).
$$

If I bound $F-T_\uparrow$, the completed prime term, and the below-window term in absolute value, Lean adds those three budgets to bound $\lvert F-T_W\rvert$. The written contour argument gives the proposed growth bounds for those pieces. The signed upper estimate on $T_W$ remains the arithmetic input for the late windows. [Exact cutoff and error transfer](GaussianVaughanPrimeComplement.lean) · [Written contour estimates](gaussian-vaughan-log-window.md) · [Source replay and axioms](gaussian-vaughan-prime-complement-audit.txt)
