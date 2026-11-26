# The Gaussian sum with seventh powers removed

I keep the same quartic $K$, the same Gaussian base $k=\mathbb Q(i)$, and the same archived ideal character $\chi$. Write $G(w)=L_k(w,\chi)$ for the checked Gaussian factor. If I only keep ideals with every prime-ideal exponent below $7$, the exponentially weighted sum has Mellin transform $\Gamma(s)G(s)/G(7s)$. The checked reflection makes every Gaussian zero in the critical strip give a pole of the same order at $s=\rho/7$. [Lean pole order and quartic equivalence](GaussianSeventhFreeMellin.lean) · [Clean build and axioms](gaussian-seventh-free-audit.txt)

## Which ideals survive

At each prime ideal $\mathfrak q$, put $u=(N\mathfrak q)^{-s}$. The character is quadratic, including $0$ at its ramified primes, so $\chi(\mathfrak q)^7=\chi(\mathfrak q)$. If I multiply its ordinary Euler factor by $1-\chi(\mathfrak q)u^7$, I get

$$
\frac{1-\chi(\mathfrak q)u^7}{1-\chi(\mathfrak q)u}
=\sum_{j=0}^{6}\chi(\mathfrak q)^j u^j.
$$

Lean checks the product of these local identities for every rational prime, keeping the separate inertia degree of each ideal above it. At $5$, both signed ideals have character $+1$. At norm $5^7$, the original coefficient is $8$ and the restricted one is $6$, because the surviving exponents are $(1,6),\ldots,(6,1)$. The cutoff is on each ideal valuation. [Exact local Euler theorem](GaussianSeventhFreeEuler.lean) · [Archived prime signs](gaussian-inert-windows.md#which-positive-count-to-bound)

Define

$$
S(X)=\sum_{\substack{\mathfrak a\ne 0\\
 v_{\mathfrak q}(\mathfrak a)<7\ \forall\mathfrak q}}
 \chi(\mathfrak a)e^{-N\mathfrak a/X}.
$$

In the written global calculation, the absolutely convergent Euler products in $\Re s>1$ give $G(s)/G(7s)$. Integrating $e^{-N\mathfrak a/X}X^{-s-1}$ gives $\Gamma(s)(N\mathfrak a)^{-s}$, so the Mellin integral from $0$ to $\infty$ is the expression in Lean. The absolute interchange follows by domination with $\Gamma(\Re s)\sum_{\mathfrak a\ne0}(N\mathfrak a)^{-\Re s}$.

## Why seven works

I use $b=873333/10^6$ as a rational bound above Liu's $\theta_G$. The published preprint supplies the zero-free input for $G$. If $G(\rho)=0$ in the strip, then $0<\Re \rho\le b$, so

$$
\Re(1-\rho/7)\ \ge\ 1-b/7\ >\ b.
$$

The Lean Mellin reflection identifies zeros of $G(s)$ and $G(1-s)$ in the strip. The numerator $G(\rho/7)$ is therefore nonzero, and $\Gamma(\rho/7)$ is also nonzero. The substitution $s\mapsto7s$ has nonzero derivative. Lean checks that a zero of order $m$ at $\rho$ gives meromorphic order $-m$ at $\rho/7$. [Liu, Theorem 7.33](https://hexagonmath.org/pdf/2611.00741v1#page=66) · [Lean numerator and order proofs](GaussianSeventhFreeMellin.lean)

If $S(X)=O_\varepsilon(X^{1/14+\varepsilon})$ for every $\varepsilon>0$, the defining Mellin integral is analytic on $\Re s>1/14$. The integral near $X=0$ is entire by exponential decay. The identity on $\Re s>1$ then rules out any pole with $\Re s>1/14$. With the rational Dirichlet input, Lean proves the equivalence between analyticity on this half-plane and Dedekind RH for the quartic. The printed inputs are $h_D$ for the rational cofactors and $h_{\rm Free}$ for the bound $b$. [The exact Lean theorem and output](gaussian-seventh-free-audit.txt)

The written converse uses exponential smoothing. Under the quartic conclusion and $h_{\rm Free}$, I can shift the inverse Mellin contour to any fixed $\Re s>1/14$. In a closed strip to the right of the denominator's zero-free boundary, its inverse has polynomial vertical growth. This follows by applying Borel–Carathéodory to $\log G$ on disks centered in the absolutely convergent half-plane, using polynomial growth for $G$ on bounded vertical strips. Stirling's estimate for $\Gamma$ makes the shifted integral absolutely convergent. The same argument with Liu's unconditional boundary gives $S(X)=O_\varepsilon(X^{\theta_G/7+\varepsilon})$, where $\theta_G/7$ is about $0.124762$. [Reciprocal vertical growth, Liu Lemma 4.3](https://hexagonmath.org/pdf/2611.00741v1#page=6)

## The actual signed sum at the shorter scale

If I expand the seventh-power-free indicator as $\sum_{\mathfrak d^7\mid\mathfrak a}\mu_k(\mathfrak d)$, the same sum becomes

$$
S(X)=\sum_{\mathfrak d\ne0}
  \mu_k(\mathfrak d)\chi(\mathfrak d)\,
  \Theta\!\left(\frac{(N\mathfrak d)^7}{X}\right).
$$

Here $\Theta$ is the original Gaussian theta series and $\mu_k$ is ideal Möbius. The double series is absolutely convergent for fixed $X>0$, since $e^{-t}\ll_\sigma t^{-\sigma}$ with $\sigma>1$ gives the majorant $X^\sigma\zeta_k(\sigma)\zeta_k(7\sigma)$ up to a constant. Write $C=\sqrt{26509772707289}/\pi$ and $X=CY^7$. Lean checks reflection and both tails for the exact kernel $H(v)=\Theta(v^7/C)$. In particular $H(v)=v^{-7}H(v^{-1})$, and the upper tail is bounded by $2e^{-v^7/C}$ whenever $v^7/C\ge2$. The lower tail follows by the same bound at $v^{-1}$.

In these units the remaining arithmetic estimate is a square-root bound on the ideal Möbius sum with the fixed weight $H(N\mathfrak d/Y)$, uniformly at large $Y$. I checked the two expansions on exact signed coefficients through norm $8192$ at $X=128$. Through that cutoff the only nontrivial seventh-power divisor comes from $1+i$, which has character $+1$. Directly summing the restricted coefficients gives about $15.02921586$, and subtracting $\Theta(1)$ from $\Theta(1/128)$ gives the same value to eight decimal places. The tail of each series cut at norm $8192$ is at most $\sum_{n>8192}n e^{-n/128}$. [Lean reflection and tail bounds](GaussianSeventhFreeMellin.lean)

## The same calculation for a number field

For a number field $F$, take the untwisted count of its nonzero ideals with every prime-ideal exponent below $7$, with the same exponential weight. Its Mellin expression is $\Gamma(s)\zeta_F(s)/\zeta_F(7s)$. Its linear main term is $X\,\operatorname{Res}_{s=1}\zeta_F(s)/\zeta_F(7)$. The same written reflection argument excludes cancellation at every $\rho/7$ using the uniform bound from Liu. Subtracting the main term and shifting the contour shows that the field's RH is equivalent to an $O_{F,\varepsilon}(X^{1/14+\varepsilon})$ remainder for all $\varepsilon>0$. This last equivalence is a written application of the Dedekind functional equation, Euler product, and vertical growth, with the quartic's analytic step checked in Lean. [Dedekind functional equation](https://websites.umich.edu/~lagarias/doc/numberthzeta.pdf) · [Uniform zero-free theorem](https://hexagonmath.org/pdf/2611.00741v1#page=66)
