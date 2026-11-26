# The pole at the same Gaussian zero

I use $G$ for the archived Gaussian factor, $\Lambda$ for its completed Mellin reading, and $L(n)$ for the signed Gaussian von Mangoldt coefficients. I write $H(v)=\Theta(v^7/c)$, where $c$ is the archived theta scale.

$$
H_D(v)=H(v)-\sqrt{2}\,H(2v),\qquad
M(z)=\bigl(1-2^{1/2-z}\bigr)\frac{\Lambda(z/7)}7.
$$

If $F(X)=\sum_{n\ge1}L(n)H_D(n/X)$, the absolute convergence calculation gives

$$
\int_0^\infty F(X)X^{-z-1}\,dX
 = M(z)\frac{-G'(z)}{G(z)}
\qquad(\Re z>1).
$$

If I start the integral at one, I subtract the explicit entire function $E(z)=\int_0^1 F(X)X^{-z-1}\,dX$. Lean supplies the transform from the archived coefficients, the power bounds for $F$, and the proof that $E$ is entire. [Theta and endpoint bounds](GaussianVaughanKernelBounds.lean) · [Actual series and Mellin integral](GaussianVaughanMellinSeries.lean)

If $G$ has a zero of multiplicity $r$ at $\rho$ with $\Re\rho>1/2$, the continued reading has a simple pole at $\rho$ with residue $-rM(\rho)$. The scale difference stays nonzero there. With the Gaussian zero-free input $\Re z>873333/10^6$, reflection protects $\Lambda(\rho/7)$ from vanishing. Since $E$ is entire, the integral from one keeps that same pole and residue. [Lean pole and residue](GaussianVaughanWindowCriterion.lean)

## Inputs to the quartic theorem

I use the signed sum $T_W(X)$ from the complementary prime window, with the leading minus sign included. The primes lie in $(X/(\log X)^5,2X/(\log X)^{5/2}]$ and the cofactors are at most $(\log X)^{8/3}$. [Cutoff formula and written error estimate](gaussian-vaughan-log-window.md)

- If $\lvert F(X)-T_W(X)\rvert\le C X^{3/8}(\log X)^{8/3}$ eventually, Lean absorbs that error into the window constant.
- If for each $1/2<\theta<1$ there are $\delta>0$ and $C_\theta\ge0$ with $T_W(X)\le C_\theta X^\theta$ throughout arbitrarily late intervals $[Y,Y^{1+\delta}]$, Lean supplies the late-window bound for $F$.
- If I supply both inequalities, the rational Dirichlet critical-line input, the Gaussian zero-free input, and the shared real-axis positivity, Lean gives the critical-line theorem for the archived quartic's Dedekind zeta.

The contour-shift approximation remains a written estimate and an explicit premise of this Lean theorem. The late-window upper bound remains the arithmetic input. The real-axis positivity argument has its own Lean 4.19.0 replay. [Exact theorem and premises](GaussianVaughanMellinSeries.lean) · [Source replay and axioms](gaussian-vaughan-mellin-series-audit.txt) · [Real-axis positivity audit](quartic-real-positivity-audit.txt)
