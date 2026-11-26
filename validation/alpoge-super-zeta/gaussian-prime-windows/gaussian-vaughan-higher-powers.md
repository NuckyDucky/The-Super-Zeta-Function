# The higher powers on the Mellin contour

I split the higher-prime-power coefficient into the square and the powers $p^j$ with $j\ge3$. If $\sigma>1/3$, the latter terms are dominated by

$$
\frac{2}{1-2^{-\sigma}}\sum_p\frac{\log p}{p^{3\sigma}}.
$$

Lean proves absolute convergence and analyticity on that half-plane, and a bound uniform in height on each closed half-plane inside it. At $\sigma=3/8$ the exponent in the majorant is $9/8$. [Lean prime-power bound and exact split](GaussianVaughanPrimePowers.lean)

## The square reading at twice the coordinate

I put $D=26509772707289$. At level $4D$, the four characters are the principal character, the lifted $\chi_{-4}$, the product of the three conductor Legendre characters, and the product of the last two. The square coefficient combines those four values with signs $+,+,+,-$. At a prime dividing $2D$ the four values vanish and the original square weight contributes $1$. Moving the coefficient from address $p$ to $p^2$ sends its rational Dirichlet-series argument to $2z$. [Exact character identity and square dilation](GaussianVaughanRationalSquares.lean)

If I replace the rational prime terms by their full logarithmic derivatives, I subtract the rational powers of exponent at least two at $2z$. Those terms also converge absolutely on the $3/8$ contour. Together with the finite exceptional-prime contribution and the Gaussian cubes and higher powers, they give a correction bounded uniformly for $\Re z\ge3/8$. [Uniform correction](GaussianVaughanHigherContinuation.lean)

## Through the principal pole

I use the existing factor $1-2^{1/2-z}$. The principal function at $2z$ has its pole at $z=1/2$. Lean uses the actual residue at the common level to extend the normalized principal function, and a divided difference of the scale factor to absorb the pole in its logarithmic derivative. If I supply the rational Dirichlet critical-line input, every filtered logarithmic derivative is analytic for $\Re z>1/4$. [Lean proof at the removed pole](GaussianVaughanFilteredDirichlet.lean)

Combining these pieces gives an analytic continuation of the weighted Gaussian higher-power term and the completed-prime transform for $\Re z>1/3$, with the same Mellin values as the original series on $\Re z>1$. The contour calculation still needs vertical growth and decay bounds. The exact signed cutoff and the late-window bound remain the inputs for the quartic implication. [Exact continuation theorem](GaussianVaughanHigherContinuation.lean) · [Source replay and axiom audit](gaussian-vaughan-higher-powers-audit.txt)
