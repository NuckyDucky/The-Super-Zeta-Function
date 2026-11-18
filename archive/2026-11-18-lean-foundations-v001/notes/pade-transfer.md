# Positive-measure Padé enclosures for Nick's fixed phases and Dottie endpoint

This note transfers Borghi's 2024 positive-measure representation into rigorous, computable lower and upper bounds for the reciprocal fixed phases and logarithmic parameter. The approximation variable, pushforward measure and endpoint extension are explicit. The analytical result holds at every order; the companion interval script certifies concrete enclosures.

## 1. The exact 2024 input and its variable

Let \(0<\varepsilon<1\), and set

\[
\chi=\sqrt{1-\varepsilon^2},\qquad
\lambda=\chi-\operatorname{artanh}\chi,\qquad r=e^\lambda\in(0,1).
\]

Borghi's complex Kapteyn function has the representation

\[
\mathbb S_\varepsilon(z)
=z\int_0^1\frac{\rho_\varepsilon(t)}{1-zt}\,dt,
\quad z=e^{\lambda+iM},\quad 0\le\rho_\varepsilon(t)\le2,
\tag{1}
\]

with exact moments

\[
m_j(\varepsilon)=\int_0^1t^j\rho_\varepsilon(t)\,dt
=\frac{2J_{j+1}((j+1)\varepsilon)}{(j+1)r^{j+1}}.
\tag{2}
\]

These are equations (15)–(17), (23) and (26) of [Borghi, *On the Bessel Solution of Kepler's Equation*, 2024](https://www.mdpi.com/2227-7390/12/1/154), [author full text](https://arxiv.org/html/2312.01437v2). The density is \(2\theta(t)/\pi\), where \(\theta(t)\) decreases from \(\pi\) to zero according to the inverse defined in that paper. Positivity and compact support are the inputs used below.

At mean anomaly \(M=\pi/2\), \(z=ir\). The real Kepler correction is \(u=\operatorname{Im}\mathbb S_\varepsilon(ir)\), so (1) gives the positive real integral

\[
\boxed{u(\varepsilon)=r\int_0^1
\frac{\rho_\varepsilon(t)}{1+r^2t^2}\,dt,
\qquad u=\varepsilon\cos u.}
\tag{3}
\]

Introduce the positive pushforward measure \(\eta_\varepsilon\) under \(w=t^2\). Its moments are

\[
M_j=\int_0^1w^j\,d\eta_\varepsilon(w)=m_{2j}.
\]

For each fixed \(\varepsilon\), define the auxiliary resolvent

\[
F_\varepsilon(x)=\int_0^1\frac{d\eta_\varepsilon(w)}{1+xw}
=\sum_{j\ge0}(-1)^jM_jx^j\quad(|x|<1).
\tag{4}
\]

The desired value is \(u(\varepsilon)=rF_\varepsilon(r^2)\). Here \(x\) is an auxiliary resolvent variable and the measure itself depends on \(\varepsilon\). Formula (4) preserves Borghi's original variable roles while producing the real positive kernel needed for enclosures.

## 2. The positive measure extends to the Dottie endpoint

Set \(\varepsilon=1\), \(\lambda=0\), \(r=1\). The moments have the finite limits

\[
m_j(1)=\frac{2J_{j+1}(j+1)}{j+1}.
\]

The positive measures \(\rho_\varepsilon(t)dt\) have mass at most 2 and common compact support \([0,1]\). Any sequence \(\varepsilon\to1^-\) therefore has a weakly convergent subsequence. Moment continuity gives the displayed moments for every subsequential limit. Uniqueness for the compact Hausdorff moment problem follows from density of polynomials in \(C[0,1]\), so the positive limit measure is unique.

The kernels in (3) converge uniformly as \(r\to1\), and the unique root of \(u=\varepsilon\cos u\) in \((0,1)\) varies continuously to the Dottie number. Consequently

\[
\boxed{d=\int_0^1\frac{d\eta_1(w)}{1+w},
\qquad d=\cos d.}
\tag{5}
\]

The limit measure has infinite support by an elementary domination argument. Every prelimit measure satisfies \(0\le\rho_\varepsilon(t)dt\le2dt\). For every nonnegative continuous test function this inequality passes to the weak limit, so the limit is also dominated by \(2dt\). Its mass is \(2J_1(1)>0\), hence it is nonzero and has no atoms. The injective pushforward \(t\mapsto t^2\) also has no atoms and therefore has infinite support. Thus all the moment matrices needed at finite quadrature order are strictly positive definite, including at the endpoint.

## 3. The enclosure theorem

Let \(G_n(x)\) denote the Padé approximant of type \([n-1/n]\) to (4), and \(R_n(x)\) its type \([n/n]\) approximant. All coefficients use the moments of the fixed measure \(\eta_\varepsilon\).

**Theorem (all-order Padé transfer).** For every \(0<\varepsilon\le1\), every integer \(n\ge1\), and \(x>0\),

\[
G_n(x)<F_\varepsilon(x)<R_n(x).
\]

In particular,

\[
\boxed{u_n^-=rG_n(r^2)
<u(\varepsilon)<rR_n(r^2)=u_n^+.}
\tag{6}
\]

The lower rational function is the \(n\)-node Gaussian quadrature of the positive measure. The upper rational function is the Gauss–Radau quadrature with the node zero and \(n\) free nodes. Formula (6) is valid through the Dottie endpoint.

Moreover, put
\[
h=\sqrt{1+r^2},\qquad q=\frac{h-1}{h+1},\qquad q_*=3-2\sqrt2.
\]
The bracket width has the explicit uniform geometric bound
\[
\boxed{0<u_n^+-u_n^-\le8J_1(\varepsilon)q^{2n}
\le4q_*^{2n}\qquad(0<\varepsilon\le1).}
\tag{6a}
\]
Thus the two-sided approximation has a convergence rate uniform through the Dottie endpoint.

### Proof

The positive measure on \([0,1]\) with infinite support gives a strictly positive moment functional. Its monic degree-\(n\) orthogonal polynomial has \(n\) simple roots in \((0,1)\). The resulting Gaussian rule has positive weights and is exact through degree \(2n-1\). For

\[
f_x(w)=(1+xw)^{-1},
\qquad f_x^{(k)}(w)=(-1)^kk!x^k(1+xw)^{-k-1},
\]

the Hermite interpolant at the Gaussian nodes has remainder

\[
f_x(w)-H(w)=\frac{f_x^{(2n)}(\xi_w)}{(2n)!}\,p_n(w)^2\ge0.
\]

Integration gives the Gaussian lower bound, strict because the measure has infinite support and the integrand is positive away from finitely many nodes.

For the Radau rule, take the degree-\(n\) orthogonal polynomial for the measure \(w\,d\eta_\varepsilon(w)\), include zero as an additional node, and interpolate the function value at zero and its value and derivative at the \(n\) interior nodes. The rule is exact through degree \(2n\), with positive weights. The remainder is

\[
f_x(w)-H_R(w)=
\frac{f_x^{(2n+1)}(\zeta_w)}{(2n+1)!}\,w\,p_n(w)^2\le0.
\]

Its integral gives the strict upper bound.

Expanding the Gaussian rational rule in \(x\) matches moments through degree \(2n-1\); its denominator and numerator have degrees \(n\) and at most \(n-1\). Hence it is the Padé approximant \([n-1/n]\). The Radau rule has denominator degree \(n\), numerator degree at most \(n\), and matches moments through degree \(2n\), so it is \([n/n]\). Evaluating at \(x=r^2\) and multiplying by positive \(r\) proves (6). ∎

Only finitely many ordinary Bessel values are needed: the lower approximant uses \(M_0,\ldots,M_{2n-1}\), while the upper uses \(M_0,\ldots,M_{2n}\). Thus the largest ordinary Bessel order is \(4n+1\).

### Proof of the uniform geometric width

For \(x=r^2\), the exact Chebyshev expansion of the resolvent is
\[
\frac1{1+xw}=\frac1h\left[1+2\sum_{k\ge1}(-q)^kT_k(2w-1)\right],
\qquad0\le w\le1.
\]
This follows from the Poisson-kernel identity and \(q=(h-1)/(h+1)\). Since \(|T_k|\le1\), its degree-\(N\) truncation has uniform error at most
\[
E_N=\frac2h\frac{q^{N+1}}{1-q}.
\]
Both positive quadrature rules have total weight \(M_0\). A rule exact on the chosen polynomial has integration error at most \(2M_0E_N\). Apply this at degrees \(2n-1\) and \(2n\), then multiply by \(r\) and add the two one-sided errors:
\[
u_n^+-u_n^-\le\frac{4rM_0}{h}
\frac{q^{2n}(1+q)}{1-q}=4rM_0q^{2n}=8J_1(\varepsilon)q^{2n}.
\]
Here \((1+q)/(1-q)=h\) and \(rM_0=2J_1(\varepsilon)\). The elementary Poisson integral for \(J_1\) gives \(0<J_1(\varepsilon)\le\varepsilon/2\le1/2\), while \(0<r\le1\) gives \(q\le q_*\). This proves (6a). ∎

## 4. Propagation into the Hidden Work

Nick's quarter-phase fixed pair is

\[
a=\varepsilon\sin u,\quad
L=iy,\quad y=\varepsilon e^{-a},\quad
P=e^{a+iu},\quad Q=\overline P,
\quad\mu=\varepsilon^2.
\tag{7}
\]

Take any certified bracket \(0<\ell\le u\le h<1\) from (6). Monotonicity of sine on this interval yields

\[
\boxed{\varepsilon e^{-\varepsilon\sin h}
\le y\le
\varepsilon e^{-\varepsilon\sin\ell}.}
\tag{8}
\]

The phases are enclosed by interval evaluation of \(\exp(\varepsilon\sin[\ell,h]\pm i[\ell,h])\). There are simple explicit sensitivity bounds:

\[
\boxed{\operatorname{diam}(y)\le\varepsilon^2(h-\ell),}
\]
\[
\boxed{\operatorname{diam}\{P(u):u\in[\ell,h]\}
\le e^{\varepsilon\sin h}\sqrt{1+\varepsilon^2}\,(h-\ell).}
\tag{9}
\]

Indeed, \(|y'(u)|=\varepsilon^2e^{-\varepsilon\sin u}\cos u\le\varepsilon^2\), and
\(|P'(u)|=e^{\varepsilon\sin u}\sqrt{1+\varepsilon^2\cos^2u}\). The same phase bound holds for \(Q\).

These finite constants remain bounded at \(\varepsilon=1\). Thus the approximation transfers to the Dottie fold location \(y_*=e^{-\sin d}\) and the two phases with explicit, computable errors. It uses a regular eccentricity coordinate to enclose the parameter where the dynamical projection folds.

## 5. Certified computation

The script `certify_pade.py` uses 1024-bit Arb ball arithmetic. It constructs the moments directly from (2), solves the two interval Padé systems, and takes outward endpoints for (6). Every bound contains an independent 600-step exact-dyadic bisection bracket for the unique root of \(u-\varepsilon\cos u\). It also propagates the bracket through (7) and checks that both complex fixed-equation residual balls contain zero.

Twenty-one enclosures passed at \(\varepsilon=0.5,0.9,1\) and \(n=1,2,4,8,16,24,32\). Selected certified bracket widths, rounded upward for display:

| \(n\) | \(\varepsilon=0.5\) | \(\varepsilon=0.9\) | \(\varepsilon=1\), Dottie |
|---:|---:|---:|---:|
| 4 | \(1.252\times10^{-9}\) | \(4.636\times10^{-7}\) | \(7.760\times10^{-7}\) |
| 8 | \(3.386\times10^{-18}\) | \(2.431\times10^{-13}\) | \(5.843\times10^{-13}\) |
| 16 | \(2.487\times10^{-35}\) | \(6.714\times10^{-26}\) | \(3.301\times10^{-25}\) |
| 32 | \(1.344\times10^{-69}\) | \(5.129\times10^{-51}\) | \(1.051\times10^{-49}\) |

Exact rational outward endpoints, denominator coefficient balls, propagated parameter/phase intervals and all finite scope records are saved in `pade-enclosures.json`.

## Source roles and contribution

Borghi supplies the published Stieltjes representation and its positive moment density in the transformed phase variable. The Gaussian/Radau inequalities are proved above from positive-measure interpolation. Nick's construction supplies the fixed-pair observable map (7). This continuation pushes the measure through \(t\mapsto t^2\), applies the two-sided positive-resolvent approximation at the reciprocal quarter-phase, proves its Dottie endpoint extension, and propagates the resulting certified bounds into \(L,P,Q\). These are explicit analytical and computational consequences obtained from the supplied current and Hidden Work.
