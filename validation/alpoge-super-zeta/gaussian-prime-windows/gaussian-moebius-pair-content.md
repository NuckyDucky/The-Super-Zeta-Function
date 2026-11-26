# The product of the two primitive norms

I split the two coprime norms left by the common-divisor calculation as $u=h^2k$ and $v=j^2l$. For fixed common divisor $d$, put $R=\sqrt Y/d$. A smooth cutoff in the product $kl$ through $R^{1001/1000}$ gives $O_\varepsilon(Y^{69977449/140000000+\varepsilon})$ after adding the remaining common divisors. The exponent is approximately $0.499839$. This uses ordinary RH and Liu's Gaussian zero-free bound. The square parts of both inputs are allowed to vary. [Common-divisor calculation](gaussian-moebius-common-divisor.md) · [Lean identities](GaussianMoebiusPairContent.lean) · [Independent replay and axioms](gaussian-moebius-pair-content-audit.txt)

## The four local choices

I keep the same reciprocal Gaussian coefficients $A$, with local values $1,-a_p,c_p,0,\ldots$, where $c_p=(\chi_{-4}\chi_D)(p)$ and $D=26509772707289$. The coefficient $a_p$ retains the signed sum over the marked primes. The squarefree variables $h,j,k,l$ are pairwise coprime because $u,v$ are coprime and only prime exponents $0,1,2$ can give a nonzero term.

Use $U=p^{-s}$ and $V=p^{-t}$ for $h,j$, and $X=p^{-z}$ and $S=p^{-w}$ for $k,l$. At $p\nmid d$ the local factor is

$$
1+c_p(U+V)-a_p(X+S).
$$

At $p\parallel d$ it is $a_p^2-a_pc_p(X+S)$. At $p^2\parallel d$ it is $c_p^2$. Higher exponents give zero. The specialization $U=X^2$, $V=S^2$ gives the original two-variable factor. Lean verifies these identities against the actual prime-power coefficients and proves $c_p^3=c_p$, including at the conductor.

I checked all $512^2$ ordered pairs by first generating the signed Gaussian coefficients with the archived Legendre readings, then separately regrouping each coefficient product through these four variables. All products agreed. For example, $(m,n)=(242,245)$ has $d=1$ and $(h,j,k,l)=(11,7,2,5)$. The coefficient product is $2$, and $kl=10$ lies below $\sqrt{242\cdot245}$. Both primitive factors enter this example.

## The correction for coprime square parts

Put $\psi=\chi_{-4}\chi_D$, a nonprincipal quadratic character. Write $c=c_p$ and $a=a_p$ locally, and let $Q(x)=1-ax+cx^2$. The rational part of the four-variable Euler product contains $1+c(U+V)$. To separate the two square parts, I use

$$
\frac{(1+cU)(1+cV)(1-c^2UV)}
{(1-c^3U^2V)(1-c^3UV^2)}.
$$

If I subtract this expression from $1+c(U+V)$, the common numerator is exactly

$$
-c^4UV(U^2+UV+V^2)+c^6(UV)^3(1+c(U+V)).
$$

Every rational monomial remaining has degree at least four. The other product is $Q(X)Q(S)$, the two ordinary inverse Gaussian Euler factors. Lean's second correction identity shows that additional monomials are either at least quadratic in $X,S$ or contain a rational variable and a primitive variable. The local denominators of the correction are bounded away from zero on the fixed strips. For the $Q$ factors this follows from their original products over Gaussian prime ideals and $|X|,|S|\le p^{-b}$ for $b>0$.

Thus, on the initial region of absolute convergence, the four-variable series for fixed $d$ is

$$
F_d(s,t,z,w)
=
\frac{L(s,\psi)L(t,\psi)L(2s+t,\psi)L(s+2t,\psi)}
{L(2s,\psi^2)L(2t,\psi^2)L(s+t,\psi^2)G(z)G(w)}
\mathcal E_d(s,t,z,w).
$$

The correction product $\mathcal E_d$ converges normally if $\Re s,\Re t>1/4$ and $\Re z,\Re w>b$ with $b=0.8734$. In this region every remaining monomial has total real exponent greater than one. The factors at $p\mid d$ are bounded by a constant per prime on closed substrips, so $\mathcal E_d=O_\delta(d^\delta)$ there for each $\delta>0$. The three $\psi^2$ series are ordinary zeta with finitely many factors removed. Ordinary RH gives holomorphic reciprocals on these strips, with zeros at their principal poles. Liu's bound gives holomorphic $1/G$ there. The reciprocals have polynomial vertical growth by Borel–Carathéodory in smaller closed strips of the zero-free half-planes, regularizing the principal poles before taking logarithms. These product and contour steps are written arguments using the Lean polynomial identities. [Liu's zero-free bound](https://hexagonmath.org/pdf/2611.00741v1#page=66)

## Inserting the product cutoff

Start with the six scales $Y_\ell=Y/2^\ell$ and the matched cutoffs from the common-divisor calculation. Set $U_0=Y^{3/14}$. For the reduced norms $u,v$ use a smooth cutoff equal to one when both are at most $U_0$ and supported where both are at most $2U_0$. The previous square-root bound for the small ratios applies with this factor, since it weights each ratio independently of $\ell$ and the constant factor of two preserves the bound. Its complement is supported only when $\max(u,v)>U_0$. Therefore on the remaining terms $d\le 2Z/U_0=O(Y^{2/7}(\log Y)^{1/14})$.

Let $R_\ell=\sqrt{Y_\ell}/d$, $R=\sqrt Y/d$, and $\lambda=\sqrt Y/Z$. At each fixed $d,\ell$ the weight in the pair sum is $f_\ell(u/R_\ell,v/R_\ell)$, with the previously used factors $K(xy)W(\lambda x)W(\lambda y)$ and the smooth complement in the reduced norms. I insert $V_0(kl/B_0)$ where $V_0$ is smooth, equals one through $1$, and is zero from $2$ on. The two-variable Mellin transform of $f_\ell$ is rapidly decreasing on closed vertical strips of positive real part, up to fixed powers of $\lambda^{-1}$. Integrating by parts in logarithmic variables gives the uniform bound because the cutoffs' logarithmic derivatives are bounded at every scale. The transform of $V_0$ has the corresponding vertical decay on positive lines.

On initial lines with all series absolutely convergent, the integrand after the three Mellin inversions is

$$
\widehat f_\ell(z,w)\widehat V_0(q)\,
R_\ell^{z+w} B_0^q\,F_d(2z,2w,z+q,w+q).
$$

I move $z,w$ to real part $z_0=0.1251$ with $q$ far enough to the right. Then I move $q$ to real part $b-z_0=0.7483$, so both primitive arguments lie at $b=0.8734$. The established holomorphic regions justify the successive shifts and the rapid decay bounds the vertical integrals. Lean checks the strict convergence inequalities for these coordinates. The resulting estimate is $O_\delta(d^\delta R^{2z_0}B_0^{b-z_0}(\log Y)^C)$, since the six $R_\ell$ differ by fixed factors.

If $B_0=R$, the local exponent is $z_0+b=0.9985$. With $B_0=R^{1001/1000}$ it is $\gamma=0.9992483<1$. Up to logarithms and the arbitrarily small power allowance, summing over $d$ gives

$$
\sum_{d\le2Z/U_0}(\sqrt Y/d)^\gamma
\ll Y^{\gamma/2+(2/7)(1-\gamma)}(\log Y)^{(1-\gamma)/14}.
$$

The power of $Y$ is $69977449/140000000$. For $B_0=R$ the analogous exponent is $13991/28000$, approximately $0.499679$. Both apply to the corresponding smoothly cut portion of the six-scale sum. With rational Dirichlet GRH for the small-ratio result and Liu's Gaussian bound, the remaining square-root obligation has the extra restriction $kl>R^{1001/1000}$. On its support the two square parts satisfy $hj\le 2\lambda^{-1}R^{999/2000}$. [Original square-root criterion](gaussian-seventh-free.md#why-seven-works)
