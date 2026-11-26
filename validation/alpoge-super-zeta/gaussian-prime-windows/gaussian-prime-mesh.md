# Certifying the Gaussian prime ramp between spaced samples

If I know the corrected prime ramp at the ends of an interval, I can bound it at every point inside using the negative slope jumps in that interval. Lean checks the exact chord gap, its one-sided bound, and the transfer from cofinal sample meshes to the Dedekind critical-line statement for the archived quartic. This uses the same prime-only ramp and linear correction already in the field proof. [Previous prime-power knot test](GaussianPrimeWindowKnots.lean) · [Lean proof](GaussianPrimeMesh.lean) · [Independent replay and axioms](gaussian-prime-mesh-audit.txt)

## The gap between two readings

Write $F(x)$ for the archived Gaussian prime-only ramp and $\gamma_p=a(p)\log p/p$ for its slope jump at a prime $p$, using the actual quartic weight $a(p)$. Let $\ell(x)$ be the straight line through the readings at $L$ and $R$, with $L<R$. I get

$$
\ell(x)-F(x)=\sum_{L<p<R}\gamma_p
\frac{(\min(x,p)-L)(R-\max(x,p))}{R-L},\qquad L\le x\le R.
$$

The correction to the linear term cancels out of this identity. So do all primes outside the open interval. Each factor multiplying $\gamma_p$ is nonnegative and at most $(x-L)(R-x)/(R-L)$. Positive prime weights lower the ramp relative to the chord. Negative prime weights can raise it. If

$$
M^-(L,R)=\sum_{L<p<R}\max(0,-\gamma_p),
$$

then the upper error throughout the cell is at most $(R-L)M^-(L,R)/4$. Lean also proves the bound at each individual $x$ with $(x-L)(R-x)/(R-L)$ in place of $(R-L)/4$.

If the two readings obey $F(L)\le C L^\theta$ and $F(R)\le C R^\theta$, then the chord obeys $\ell(x)\le Cx^\theta$ by concavity for $0\le\theta\le1$ and $C\ge0$. If the cell error is at most $D L^\theta$, I get $F(x)\le(C+D)x^\theta$ throughout that cell. The field theorem takes the rational Dirichlet input and such sample certificates on cofinal windows, with fixed constants $C,D$ and a positive window exponent $\delta$ for each $1/2<\theta<1$. [Exact Lean premises](GaussianPrimeMesh.lean)

## How far apart I can put the samples

For integer endpoints $1\le L<R$, Lean checks the unconditional estimate

$$
\frac{R-L}{4}M^-(L,R)\le \frac{(R-L)^2\log R}{2L}.
$$

It uses $|a(p)|\le2$ and the count of integers between the endpoints. In $[X,2X]$ I can use integer spacings up to $X^{(1+\theta)/2}/\sqrt{\log(2X)}$ and keep the error at most $X^\theta/2$. This gives $O(X^{(1-\theta)/2}\sqrt{\log X})$ sample points per dyadic block. The spacing and count here follow by substituting the width into the checked bound.

I can remove the logarithm from the spacing if I use the already supplied Dirichlet critical-line result to bound the combined prime mass. Away from the fixed exceptional primes, every nonzero weight is supported on the rational primes completely split in the abelian subfield. Their combined log mass in $(L,R)$ is $(R-L)/4+O(\sqrt X\log^2 X)$ for $L,R\in[X,2X]$. I use it as a majorant for the negative weights, with each weight at most $2/L$ times $\log p$. Writing $H=R-L$, the interpolation error is then at most $H^2/(8L)+O(H X^{-1/2}\log^2X)$. At width $O(X^{(1+\theta)/2})$ this is $O(X^\theta)$. This last estimate is a written application of the rational count to the Lean inequality. [Combined class count](gaussian-dyadic-prime-window.md#the-same-cutoff-in-the-quartics-splitting-field) · [Frei–Sofos–Widmer, Theorem 1.1](https://arxiv.org/html/2610.18491v2#Thmtheorem1)

## The cells from one to two million

I used 101 equally spaced sample points from $10^6$ to $2\cdot10^6$, with spacing 10,000. Lean verifies a uniform upper error allowance of 1,050 across all 100 cells by using $R\le 2^{21}$ and $\log 2\le1$. This is the allowance between samples. The endpoint values are the separate input to the finite window certificate.

For a numerical check on the interpolation formula, I enumerated the 70,435 primes in this interval. Of those, 17,627 have nonzero archived weights. For $p\equiv1\bmod4$ I used a root $q^2=-1\bmod p$ and the sum of the Legendre signs of $-5045155\pm1027708q$. For $p\equiv3\bmod4$ the weight is zero. This computation gives $a(5)=2$, $a(13)=-2$, and $a(73)=0$ as small checks on the signs. [Exact archived prime weights](GaussianPrimeSupport.lean)

The gap is piecewise affine, so I evaluated it at the nonzero-weight primes in each cell and both endpoints. The largest observed value of $F-\ell$ was about $1.167851$ at $x=1064477$ in the cell $[1060000,1070000]$. The numerical value of that cell's negative-mass allowance was about $6.713178$. These two numbers use floating-point logarithms. The Lean theorem gives the exact inequality and the separate 1,050 allowance.

The cofinal arithmetic task is to bound the signed values at the chosen samples for each $\theta$. The interpolation theorem supplies the entire interval once it has those readings and the error budget.
