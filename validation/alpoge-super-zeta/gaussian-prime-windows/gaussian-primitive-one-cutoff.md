# One cutoff on the primitive squarefree pair

I keep the same Gaussian factor $G$ and its actual signed Möbius coefficients $A$. If I restrict both input norms to be squarefree and coprime, then a finite Euler multiplier lets me bound either one-cutoff sum by $O_\varepsilon(Y^{1/2+\varepsilon})$. The two-cutoff sum then reduces to one explicit signed squarefree sum, with the same error. Its Euler factors show exactly where the Gaussian zero question is still present. [Previous splitting](gaussian-moebius-pair-content.md) · [Lean local identities](GaussianPrimitiveOneCutoff.lean) · [Build and axiom audit](gaussian-primitive-one-cutoff-audit.txt)

## Which coefficients enter

Write $D=26509772707289$, $a_p$ for the archived Gaussian prime weight, $b_p=\chi_{-4}(p)$, $e_p=\chi_D(p)$, $c_p=b_pe_p$, and $Q_p(X)=1-a_pX+c_pX^2$. Put $U(n)=\mu(n)^2A(n)$, where $\mu$ here is rational Möbius. If $(k,l)=1$, each prime can occur on either side once or be absent. I can also omit a fixed finite set of primes from both inputs. In either case the two-variable series is

$$
P(s,t)=\prod_{p\ {\rm retained}}\bigl(1-a_p(p^{-s}+p^{-t})\bigr)
\qquad(\Re s,\Re t>1).
$$

For a retained prime away from $2D$, the two signs $b_p,e_p$ are in $\{-1,1\}$ and $a_p^2=(1+b_p)(1+e_p)$. Define these six inverse local factors as polynomials in $X$.

| Step | Inverse local factor $J_{j,p}(X)$ |
| --- | --- |
| $2$ | $1-c_pX$ |
| $3$ | $Q_p(X)$ |
| $4$ | $(1-b_pX)(1-e_pX)(1-c_pX)$ |
| $5$ | $Q_p(X)^3$ |
| $6$ | $(1-X)^2(1-b_pX)^2(1-e_pX)^2(1-c_pX)^3$ |
| $7$ | $Q_p(X)^9$ |

Lean checks the polynomial divisibility

$$
X^8\mid 1-a_pX-Q_p(X)\prod_{j=2}^7 J_{j,p}(X^j)
$$

for every prime away from $2D$, with the actual quartic coefficients. I also multiplied the polynomials through degree seven separately for all five allowed triples $(a_p,b_p,e_p)$. The coefficient of $X$ is $-2$ for $(2,1,1)$, $+2$ for $(-2,1,1)$, and $0$ in each of the three remaining cases. The six coefficients from degree two through seven are all zero.

## The change of weight

Let $L_j(z)=\prod_p J_{j,p}(p^{-z})^{-1}$, using the same factor formulas for every prime. These are finite products of $G(z)$, ordinary $\zeta(z)$, and the three nonprincipal Dirichlet $L$-functions of $b,e,c$. The only principal factor is $\zeta(z)^2$ in $L_6(z)$. Define

$$
D_*(z)=(1-2^{1/6-z})^2\prod_{j=2}^7L_j(jz).
$$

The dyadic square removes the pole at $z=1/6$. The resulting multiplier is entire and has no zeros in $\Re z>1/2$ by absolute convergence of the indicated products. Use this multiplier with the existing Mellin weight $\widehat H(z)=\Lambda(z/7)/7$ and set

$$
\widehat H_*(z)=D_*(z)\widehat H(z),\qquad
\widehat K_*(z)=\widehat H_*(z)G(z).
$$

The square-root bound for the Möbius sum with weight $H_*$ is equivalent to the one with weight $H$. Indeed both the Euler product and its reciprocal converge absolutely at every real exponent $1/2+\varepsilon$. Each Dirichlet monomial $n^{-z}$ replaces the scale $Y$ by $Y/n$. The two dyadic factors and their inverses act by the same rule, with inverse geometric ratio $2^{1/6-(1/2+\varepsilon)}<1$ on that bound. The inverse series can be applied on all $Y>0$ because the sums have exponential decay for small $Y$.

The kernel $K_*$ still decays as $O(e^{-c_1v^7})$ for large $v$. For the fixed dyadic powers and the absolutely convergent Euler sums, this follows by applying the upper tail of $K$ to each term of the scaled sum. The coefficients before scaling have at most polynomial growth. The Mellin integrand is entire with exponential vertical decay on fixed strips, since $\widehat H$ supplies the Gamma factor and the $L$-functions have polynomial vertical growth there. Shifting to any fixed negative line gives $K_*(v)=O_A(v^A)$ as $v\to0$ for every $A>0$. [Original kernel and tails](gaussian-balanced-moebius.md#the-kernel-after-summing-the-third-factor)

## Removing the one-cutoff terms

I use a smooth cutoff $W$ equal to one through $1$, zero from $2$ onward, and between zero and one. Set $Z=\sqrt Y\,C_Y$ with $C_Y=(c\log Y)^{1/14}$. Use $K_*(kl/Y)$ in all three sums, multiplying each term of $P$ by $W(k/Z)W(l/Z)$, by $W(k/Z)$, or by $1$. Call these three sums $\mathsf P_Z(Y),\mathsf T_Z(Y),\mathsf D(Y)$, respectively. Lean checks

$$
W(k/Z)W(l/Z)=W(k/Z)+W(l/Z)-1+(1-W(k/Z))(1-W(l/Z)).
$$

The product in the last term is supported where $kl>Z^2$. Its sum is $O_A(Y^{-A})$ for each fixed $A$, choosing $c$ large enough, by the upper tail and the polynomial bound on the total absolute weight at norm $kl$. Symmetry gives $\mathsf P_Z=2\mathsf T_Z-\mathsf D+O_A(Y^{-A})$.

To estimate $\mathsf T_Z$, divide the retained local factors by $Q_p(X)Q_p(V)\prod_{j=2}^7J_{j,p}(V^j)$, where $X=p^{-s}$ and $V=p^{-t}$. The numerator of the difference from $1$ is $O(|X|^2+|XV|+|V|^8)$. At exceptional or omitted primes I use the corresponding finite quotient. Each denominator factor is bounded away from zero on the closed positive subregions in use, since the local reciprocal factors have roots only on or outside the unit circle. This gives

$$
P(s,t)=\frac{E(s,t)}{G(s)G(t)\prod_{j=2}^7L_j(jt)}
$$

on the initial lines. The correction product $E$ is holomorphic and bounded on closed substrips strictly inside $2\Re s>1$, $\Re(s+t)>1$, $8\Re t>1$. The boundedness is uniform in both imaginary coordinates. The only possible local correction zeros are in the numerator and cause no obstruction to these shifts.

The double Mellin integral for $\mathsf T_Z$ now has integrand

$$
Y^{(s+t)/2}C_Y^{s-t}\widehat W(s-t)\widehat H(t)
(1-2^{1/6-t})^2\frac{E(s,t)}{G(s)}.
$$

The factors at $t$ cancel exactly before the shift. Starting from $\Re s>\Re t>1$, I shift $t$ to $\tau=1-b+\delta$ while $s$ is still on its first line, then shift $s$ to $b=0.8734$. Take $0<\delta\le\min(\varepsilon,1/100)$. Liu's Gaussian zero-free bound is strictly below $b$, so $1/G(s)$ is holomorphic across this shift and of polynomial vertical growth on the closed strips. The Mellin transform $\widehat W(s-t)$ decreases rapidly in $\Im(s-t)$ for the positive real differences traversed. Together with the exponential vertical decay of $\widehat H(t)$, that gives absolute integrability and vanishing horizontal faces in the successive shifts. Lean checks all four contour inequalities and $(b+\tau)/2<1/2+\varepsilon$. The factor in $C_Y$ is a fixed power of $\log Y$ and fits inside that strict allowance. Hence

$$
\mathsf T_Z(Y)=O_\varepsilon(Y^{1/2+\varepsilon}),\qquad
\mathsf P_Z(Y)=-\mathsf D(Y)+O_\varepsilon(Y^{1/2+\varepsilon}).
$$

This applies at each of the six previously matched scales with $Z_\ell=Z/2^{\ell/2}$. The contour and growth estimates here are written arguments. Lean checks the algebra and strict inequalities used in them. [Liu's zero-free bound and reciprocal growth](https://hexagonmath.org/pdf/2611.00741v1#page=66) · [Matched six scales](gaussian-moebius-common-divisor.md#removing-both-poles-with-the-original-scale)

## The signed sum that remains

Each squarefree $n$ gives $2^{\omega(n)}$ splits across the two ordered sides. The remaining scalar sum is therefore

$$
\mathsf D(Y)=\sum_{n\ge1}2^{\omega(n)}U(n)K_*(n/Y),
$$

with the same finite prime omissions if chosen. For example, with all primes retained, $U(65)=(-2)(2)=-4$ and the four ordered splits give coefficient $-16$ at $65$.

The Mellin integrand for this sum is $\widehat H(z)D_*(z)E(z)/G(z)$, where $E$ has factors $(1-2a_p p^{-z})/Q_p(p^{-z})^2$ at retained primes and $1/Q_p(p^{-z})^2$ at omitted primes. If I omit $2,5,13$, all retained primes below $17$ are inert and have $a_p=0$. For $p\ge17$, the size of $2a_p p^{-z}$ is less than one for $\Re z>1/2$, since $|a_p|\le2$. Both $E$ and its inverse then have absolutely convergent Dirichlet series at every exponent strictly above $1/2$. The local expansion begins with $1+O(p^{-2\Re z})$ at the retained primes. Thus this restricted scalar estimate is equivalent to the original weighted Möbius estimate by the same scale-convolution argument. At an off-line zero of $G$ in that half-plane, the factors $D_*$ and $E$ are nonzero, and the previously checked numerator theorem supplies $\widehat H\ne 0$ using Liu's bound. The pole and its order survive at the same point.

The exact squarefree sum gives an alternative target for the quartic bound. The remaining arithmetic is cancellation among the signed prime factors in that sum. [Original quartic criterion and numerator theorem](gaussian-seventh-free.md#why-seven-works)
