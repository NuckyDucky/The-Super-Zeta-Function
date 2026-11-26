# The common divisor of the two Gaussian Möbius inputs

I can bound a family of off-diagonal terms at the square-root scale. I write the two norms as $m=du$ and $n=dv$ with $(u,v)=1$. Two scale differences remove the two real poles of the series in $d$. With the rational Dirichlet critical-line result supplied, all pairs with $\max(u,v)\le Y^{3/14}$ then contribute $O_\varepsilon(Y^{1/2+\varepsilon})$ to the filtered sum. The filter is reversible at that exponent, and its Mellin factor is nonzero throughout $\Re z>1/2$. [Two-factor sum](gaussian-balanced-moebius.md) · [Lean local identities and filter](GaussianMoebiusCommonDivisor.lean) · [Independent replay and axioms](gaussian-moebius-common-divisor-audit.txt)

## The exact prime labels

Write $a_p$ for the archived Gaussian prime coefficient, $b_p=\chi_{-4}(p)$, $e_p=\chi_D(p)$, and $c_p=b_pe_p$ with $D=26509772707289$. For the actual grouped Möbius coefficients $A$,

$$
A(1)=1,\qquad A(p)=-a_p,\qquad A(p^2)=c_p,\qquad A(p^j)=0\quad(j\ge3).
$$

The series of $A$ is $1/G$ for $\Re z>1$, because convolution with the signed ideal coefficients is the identity. The local coefficients come from the product over actual Gaussian prime ideals, including at $2$ and the conductor. Lean checks the displayed prime-power formula against that product. Multiplicativity follows from the grouped ideal coefficients and the splitting of ideals of coprime norms. [Exact prime-power coefficients](GaussianMoebiusCommonDivisor.lean) · [Archived Möbius inverse](GaussianBalancedMoebius.lean)

For a fixed exponent $j$ of $p$ in $d$, use $U=p^{-s}$ and $V=p^{-t}$ for the other two variables. Since at most one of $u,v$ contains $p$, the local factors with common exponents $0,1,2$ are

$$
C_0=1-a_p(U+V)+c_p(U^2+V^2),\qquad
C_1=a_p^2-a_pc_p(U+V),\qquad C_2=c_p^2.
$$

The higher common exponents give zero. In particular,

$$
C_0+XC_1+X^2C_2-
(1-a_p U+c_p U^2)(1-a_p V+c_p V^2)
=(X-UV)\bigl(a_p^2-a_pc_p(U+V)+c_p^2(X+UV)\bigr).
$$

The exact labels agree with the direct coefficient product for all $512^2$ ordered pairs through norm $512$, including $102441$ pairs with common divisor greater than one. I computed the signed coefficients by summing the three archived Legendre symbols over Gaussian generators, then used the convolution recurrence for $A$. For example, $(m,n)=(25,65)$ has $d=5$. The prime $5$ contributes $-a_5c_5=-2$ and the prime $13$ contributes $-a_{13}=2$, giving $-4=A(25)A(65)$. This finite test is separate from the Lean identities.

## The two real poles on a fixed ratio

Let $D_2(s)=\sum_n |A(n)|^2 n^{-s}$ and

$$
\mathcal L(s)=\zeta(s)L(s,\chi_{-4})L(s,\chi_D)L(s,\chi_{-4}\chi_D).
$$

Away from $2D$, $a_p^2=q_p=(1+b_p)(1+e_p)$ and $c_p^2=1$. If $x=p^{-s}$ and $P_p(x)=(1-x)(1-b_px)(1-e_px)(1-c_px)$, Lean proves

$$
(1+q_p x+x^2)P_p(x)
=1-(1+2q_p)x^2+4q_p x^3-(1+2q_p)x^4+x^6.
$$

The quadratic coefficient agrees with $(1-x^2)P_p(x^2)^2$ and the cubic coefficient agrees with $P_p(x^3)^{-4}$. Thus on $\Re s>1$,

$$
D_2(s)=
\frac{\mathcal L(s)\mathcal L(3s)^4}{\zeta(2s)\mathcal L(2s)^2}E(s).
$$

For good primes the local factor of $E$ is $(1+q_p x+x^2)P_p(x)P_p(x^3)^4/[(1-x^2)P_p(x^2)^2]=1+O(|x|^4)$. At the finitely many other primes I use the actual polynomial $1+a_p^2x+c_p^2x^2$ in place of $1+q_p x+x^2$. All these local denominators are nonzero for $|x|<1$. The product therefore converges normally and is bounded on closed substrips of $\Re s>1/4$.

For a fixed ordered coprime ratio $(u,v)$ put $D_{u,v}(s)=\sum_d A(du)A(dv)d^{-s}$. The same factorization holds with a modified $E_{u,v}$. At $p^j\parallel uv$ replace the squared-coefficient polynomial by $-a_p(1+c_px)$ when $j=1$, by $c_p$ when $j=2$, and by zero when $j\ge3$. Use the same denominator as above even if the original squared-coefficient polynomial has a root. The modified factors are bounded uniformly per prime on every fixed closed substrip of $\Re s>1/4$. Consequently $|E_{u,v}(s)|\ll_\delta(uv)^\delta$ there for each $\delta>0$, with the constant also depending on the substrip. This uses the bound $C^{\omega(uv)}\ll_{\delta,C}(uv)^\delta$ for any fixed $C$.

Under the rational Dirichlet critical-line result, the denominator has no zeros for $\Re s>1/4$. Its pole at $s=1/2$ gives a zero of the inverse denominator. The only possible poles in that half-plane are $s=1$ of order at most one and $s=1/3$ of order at most four. When $A(u)A(v)\ne0$, every replaced local polynomial is nonzero at real $0<x<1$, so $E_{u,v}$ is nonzero at both real points. The $\mathcal L$ factors then give those exact orders. On fixed closed strips away from the poles the quotient has polynomial vertical growth. The inverse denominator uses Borel–Carathéodory in the known zero-free half-planes, with the principal poles removed before taking logarithms. These convergence and continuation steps are written arguments using the exact Lean local factors.

At $5$, the second-moment factor is $1+4x+x^2$. Lean checks its negative root $\sqrt3-2$. Its modulus is the same $2-\sqrt3$ that appeared in the earlier reciprocal-order calculation. Here the coefficient $4$ is the square of the sum of the two equal marked prime signs. This gives an exact zero of the continued $D_2$ at $s=\log(2+\sqrt3)/\log5+i\pi/\log5$, approximately $0.818272+1.951981i$. At this point all other factors of the continuation are holomorphic and the local factor vanishes. [Lean radius identity](GaussianMoebiusCommonDivisor.lean)

## Removing both poles with the original scale

Let $Tf(Y)=f(Y/2)$ and take

$$
\widetilde M=(1-2^{1/2}T)(1-2^{1/6}T)^4 M,\qquad
F(z)=(1-2^{1/2-z})(1-2^{1/6-z})^4.
$$

The six scale readings are $Y_\ell=Y/2^\ell$, $0\le\ell\le5$. Lean proves the factor vanishes at $z=1/2,1/6$ and is nonzero on $\Re z>1/2$. The powers expose a zero of at least order four at $1/6$. Each operation is invertible on functions with the existing rapid decay as $Y\to0$, by the geometric series in $T$. The exact finite telescoping identity is in Lean. At any exponent $\alpha>1/2$ the inverse series converges on an $O(Y^\alpha)$ bound since $2^{1/2-\alpha}<1$ and $2^{1/6-\alpha}<1$. Thus the square-root target with arbitrary $\varepsilon>0$ is equivalent for $M$ and $\widetilde M$.

I use a fixed smooth cutoff $W$ equal to one through $1$, zero from $2$ onward. Start with $Z=\sqrt{Y(c\log Y)^{1/7}}$ for sufficiently large $c$. In the two-factor formula for $M(Y_\ell)$ use $Z_\ell=Z/2^{\ell/2}$ and $P_\ell(n)=A(n)W(n/Z_\ell)$. The exact algebraic identity for $P_\ell$ still applies. Its remainder has support above $Z_\ell^2$, and the earlier upper and lower theta tails give an arbitrarily small power error at each of the six readings.

For a given ratio $(u,v)$ the kernel in the $d$-sum is $J_{u,v}(d\sqrt{uv/Y_\ell})$, where

$$
J_{u,v}(r)=K(r^2)W\!\left(\lambda\sqrt{u/v}\,r\right)
                W\!\left(\lambda\sqrt{v/u}\,r\right),\qquad
\lambda=\sqrt Y/Z=\sqrt{Y_\ell}/Z_\ell.
$$

The equality of the two $\lambda$ readings matters. With the same $\lambda$ on all six scales, Mellin inversion multiplies each ratio by exactly $F(s/2)$. The transform $\widehat J_{u,v}(s)$ has rapid decay uniformly in the ratios on fixed strips. Integrating by parts in $\log r$ gives this from the bounded derivatives of $W$ with respect to $\log r$ and the decay of $K(r^2)$ and its log derivatives at both endpoints. Those derivative bounds follow by multiplying the earlier entire Mellin weight by powers of its argument and shifting on fixed strips.

After filtering, the poles at $1$ and $1/3$ are removable in $D_{u,v}(s)\widehat J_{u,v}(s)F(s/2)$. I shift to any fixed $\sigma>1/4$. A single ratio then contributes $O_\delta((uv)^\delta (Y/(uv))^{\sigma/2})$. Summing over $u,v\le U$ gives

$$
O_\delta\!\left(Y^{\sigma/2}U^{2-\sigma+2\delta}\right).
$$

For $U=Y^{3/14}$, $\sigma>1/4$ sufficiently close to $1/4$, and $\delta$ small, this is $O_\varepsilon(Y^{1/2+\varepsilon})$. At the diagonal $(u,v)=(1,1)$ alone the filtered bound is $O_\varepsilon(Y^{1/8+\varepsilon})$. The remaining square-root estimate is for the six-scale signed sum over coprime ratios with $\max(u,v)>Y^{3/14}$. On that support, the cutoff $\max(du,dv)\le2Z_\ell$ implies $d<2Z/Y^{3/14}=O(Y^{2/7}(\log Y)^{1/14})$.

I can also cut directly in $d$ with the same scaling. If the $\ell$th reading includes a smooth factor zero for $d<D_\ell$ and one for $d>2D_\ell$, where $D_\ell=D/2^{\ell/2}$, that factor is a fixed function of $r\sqrt Y/(D\sqrt{uv})$ in the $J_{u,v}$ integral. Its log derivatives are bounded uniformly in that scale. Every surviving ratio then has $u,v\le2Z/D$. If $D=Y^{1/4}$, the same pole subtraction gives $O_\varepsilon(Y^{9/16+\varepsilon})$ for this smoothly cut, six-scale portion.

## A separate bound directly on large common divisors

For fixed $d$, start with the two-variable series from $C_j$. Divide each local factor by the product of the two inverse Gaussian factors. At $p\nmid d$, the difference formula with $X=0$ makes the quotient $1+O(|UV|)$. At $p\mid d$, the quotient is bounded by a fixed constant per prime. The product is therefore $1/[G(s)G(t)]$ times a holomorphic factor bounded by $O_\delta(d^\delta)$ on closed strips with both real parts at least $b=0.8734$. This uses $|a_p|\le2$, $|c_p|\le1$, and the local lower bounds $(1-p^{-b})^2$ for each inverse Gaussian factor.

Apply two-variable Mellin inversion to $W(\lambda x)W(\lambda y)K(xy)$ with $x=u/(\sqrt Y/d)$ and $y=v/(\sqrt Y/d)$. On the fixed contour strips, log derivatives of this weight have uniformly bounded integrals after the factor $\lambda^{-O(1)}$, since $W$ cuts off both coordinates above $2/\lambda$ and $K$ and its log derivatives are bounded. Integration by parts gives vertical decay of arbitrary fixed polynomial order. The Gaussian zero-free input allows the contours at $\Re s=\Re t=b$. This gives $O_\varepsilon(Y^{b+\varepsilon}d^{-2b+\varepsilon})$ for each $d$, with the powers of $\log Y$ absorbed by changing $\varepsilon$. Summing $d\ge Y^{1/4}$ gives $O_\varepsilon(Y^{0.6867+\varepsilon})$. The same estimate holds for the six filtered readings at that common-divisor cutoff. [Liu’s Gaussian zero-free input](https://hexagonmath.org/pdf/2611.00741v1#page=66)
