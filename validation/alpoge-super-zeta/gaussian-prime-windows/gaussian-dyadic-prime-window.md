# The central prime count on $[x/2,x)$

I keep the actual Gaussian prime weight $a(p)$ and count only the primes in $[x/2,x)$. The sign is negative on the identity class and positive on the central involution. If the resulting sum stays below $A_\theta x^\theta$ throughout arbitrarily late $[Y,Y^{1+\delta_\theta}]$, for each $1/2<\theta<1$, then Lean gives Dedekind RH for the archived quartic with the rational Dirichlet input. Each reading uses one interval $[x/2,x)$ at its own $x$. The late-window hypothesis asks for that estimate at every $x$ in the larger interval. [Exact Lean criterion](GaussianDyadicPrimeWindow.lean) · [Source replay and axiom audit](gaussian-dyadic-prime-window-audit.txt)

## The Mellin factor and the sign

Write $G$ for the actual Gaussian factor and put

$$
D(x)=-\sum_{x/2\le p<x}a(p)\log p,\qquad
D_\Lambda(x)=-\sum_{x/2\le n<x}a(n)\Lambda(n).
$$

For a fixed index $n$ the cutoff weight is one on $n<x\le 2n$. Integrating $x^{-w-1}$ over that interval gives $n^{-w}(1-2^{-w})/w$. The existing Gaussian logarithmic-derivative theorem then gives

$$
\int_1^\infty D_\Lambda(x)x^{-w-1}\,dx
=\frac{1-2^{-w}}{w}\frac{G'(w)}{G(w)}
\qquad(\Re w>1).
$$

If $G$ has a zero of multiplicity $m$ at $\rho$ with $\Re\rho>1/2$, the residue of this transform is $m(1-2^{-\rho})/\rho$. Its modulus is nonzero because $|2^{-\rho}|<1$. If $\rho$ is real, the residue is positive, which is the sign in the window theorem. The sum of $|a(p^j)|\log p/(p^j)^\theta$ over $j\ge2$ converges for $\theta>1/2$. Lean uses it to absorb the higher powers in an error $C_\theta x^\theta$ with the same windows. [Mellin identity, residues and prime-power comparison](GaussianDyadicPrimeWindow.lean) · [Window theorem wrapper and the original detector](GaussianRawWindowCriterion.lean)

This route takes the rational Dirichlet result and the local bound for $D(x)$. The real residue check supplies the sign directly, and the interval selection uses only terms with $x/2\le p<x$. The constants in the local bound can depend on $\theta$. [Printed theorem and axioms](gaussian-dyadic-prime-window-audit.txt)

## The same cutoff in the quartic's splitting field

Let $L$ be the degree-eight splitting field, $z$ its central involution, and $A=\mathbb Q(i,\sqrt{26509772707289})$ its maximal abelian subfield. Write $C_g(x)$ for the sum of $\log p$ over $x/2\le p<x$ at arithmetic Frobenius $g$ in $L$, for $g=1,z$. The existing coefficient comparison gives

$$
D(x)=2\bigl(C_z(x)-C_1(x)\bigr)
$$

above a fixed cutoff. Lean instantiates the equality with arithmetic Frobenius in the actual closure. Lean checks that membership in their union is the pair of rational tests $p\equiv1\pmod4$ and $\chi_D(p)=1$. In the abelian quotient the two labels form the identity fiber, so $C_1(x)+C_z(x)$ is the log-weighted count of primes splitting completely in $A$ in that same interval, above the finite exceptional primes. [Arithmetic Frobenius comparison](GaussianClosurePrimeTrace.lean) · [Lean sum identity and central-class criterion](GaussianDyadicFrobeniusWindow.lean)

Here is the written input for the combined count. Dirichlet GRH gives the critical-line result for $\zeta_A$ by its four abelian factors. Effective Chebotarev for $A/\mathbb Q$, followed by partial summation, gives a cumulative completely split count $t/4+O(\sqrt t\log^2 t)$ with weight $\log p$. Taking the difference at $x$ and $x/2$ gives $C_1(x)+C_z(x)=x/8+O(\sqrt x\log^2 x)$. The endpoint convention changes the bound by at most $O(\log x)$. The Lean theorem takes the resulting lower bound $x/8-C_\theta x^\theta\le C_1(x)+C_z(x)$ as `hMass`. [Abelian factors and splitting classes](gaussian-biquadratic-class-character.md) · [Frei–Sofos–Widmer, Theorem 1.1](https://arxiv.org/html/2610.18491v2#Thmtheorem1)

If $C_1(x)+C_z(x)=x/8+E(x)$, then
$$
D(x)=4\bigl(C_z(x)-x/16\bigr)-2E(x).
$$
With the written bound for $E$, the new arithmetic target is the one-sided bound on $C_z(x)-x/16$ throughout arbitrarily late windows at each exponent above $1/2$. The prior route from the quartic conclusion through $\zeta_L=\zeta_A G^2$ and effective Chebotarev gives the written return to the original retained-norm $\texttt{hcut}$. [Return to the retained norm criterion](gaussian-averaged-prime-window.md#the-arithmetic-still-to-supply)

For an exact finite comparison I can use half the combined rational count as the reference. The difference between $C_z(x)$ and that reference is $D(x)/4$. The written estimate for $E$ converts the reference to $x/16$ up to $O_\theta(x^\theta)$. [Lean count identities](GaussianDyadicFrobeniusWindow.lean)
