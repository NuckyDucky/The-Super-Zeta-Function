# Field signs at the two endpoints $T_D\pm1/16$

I fixed the interval around the Dottie height before evaluating either field. At the two endpoints the real, signed completions of $\zeta_{\mathbb Q(i)}$ are both strictly positive. The sign of the quartic completion is unresolved at both endpoints. Products throughout may be divided by positive gamma moduli, which preserves their signs. [Frozen input](gaussian-endpoints-input.json) · [Base-field intervals](gaussian-base-endpoints.json) · [Quartic factor calculation and truncation proof](gaussian-hardy-endpoints.md)

Write $k=\mathbb Q(i)$, $K=k(\sqrt{-5045155+1027708i})$. Quadratic factorization gives $\Lambda_K=c\Lambda_k\Lambda_\eta$ with $c>0$ for the normalizations used here. Thus a reversal of the quartic sign across these particular endpoints would put at least one zero of $\Lambda_\eta$ on the critical line between them. The positive weight per such zero is at least $3/(9/4+1/256)=768/577$. The common base-field sign alone supplies no lower bound on the number of these zeros.

## How the base-field reading was obtained

The base-field Dedekind zeta factors as $\zeta(s)\beta(s)$, where $\beta=L(s,\chi_{-4})$. On $s=1/2+it$ I multiply each factor by the unit-modulus phase of its completing gamma factor. FLINT evaluates the zeta factor. For beta I used the following independently bounded smoothed sum. All reported interval operations use python-flint 0.9.0 at 144 bits. [Replay](check_gaussian_base_endpoints.py) · [Dirichlet functional equation](https://dlmf.nist.gov/25.15)

Put $z=(1+s)/2,\ X^2=4|z|/\pi,\ B=16$, and $\theta=\Im\log\Gamma(z)+(t/2)\log(4/\pi)$. The Gaussian Mellin integral on $\Re u=1$,

$$
I(s)=\frac1{2\pi i}\int_{(1)}\beta(s+u) X^u e^{u^2/B^2}\,\frac{du}{u},
$$

has coefficients $W(n/X)=\tfrac12\mathrm{erfc}((B/2)\log(n/X))$, by Gaussian inversion. The beta functional equation is $\beta(s)=c(s)\beta(1-s)$, where $c(s)=(4/\pi)^{1/2-s}\Gamma((2-s)/2)/\Gamma((1+s)/2)$. Shift the integral to $-1$, take the residue at zero, and substitute $u\mapsto-u$. Replacing $c(s-u)$ by $c(s)X^{2u}$ gives the approximation $I(s)+c(s)\overline{I(s)}$. In the real signed normalization this is

$$
2\sum_{n\ge1}\frac{\chi_{-4}(n)}{\sqrt n}
       \cos(\theta-t\log n)\,W(n/X).
$$

For the error put $u=1+iv,\ V=12B$. After the contour shift the Dirichlet factor on this line is bounded by $\zeta(3/2)<3$. Relative to $c(s)X^{2u}$, the gamma ratio that was replaced by 1 is

$$
D=|z|^{-u}\frac{\Gamma(\bar z+u/2)}{\Gamma(\bar z)}
              \frac{\Gamma(z)}{\Gamma(z-u/2)}.
$$

For $|v|\le V$, integrate the digamma function along the two straight segments in these ratios. First-order Euler summation gives
$\lvert\psi(y)-\log y\rvert\le(1/2+\pi/4)/|\Im y|$ for $\Re y>0,\ \Im y\ne0$, by bounding its two remainder terms by $1/(2|y|)$ and $\tfrac12\int_0^\infty |x+y|^{-2}dx$. Along both segments $|\Im y|\ge |z|-V$ at the tested heights. Integrating the variation in $\log y$ adds at most $|u|^2/[4(|z|-V)]$ over both segments. The leading logarithms cancel the factor $|z|^{-u}$. Hence

$$
|\log D|\le\frac{(1/2+\pi/4)|u|+|u|^2/4}{|z|-V}
       \le \frac{2(1+v^2)}{|z|-V}<1/2 .
$$

Here the logarithm is defined by those path integrals. Consequently $|D-1|\le2|\log D|$. On the remaining tails the gamma recurrence on $\Re u=1$ gives $|c(s-u)|=(4/\pi)|1/4+i(t-v)/2|$, so $|D-1|\le3+|v|$. With $|e^{u^2/B^2}|=e^{(1-v^2)/B^2}$, integration bounds the error in the signed beta value by

$$
\frac{3X e^{1/B^2}}{2\pi}
\left[\frac{4(B\sqrt\pi+B^2)}{|z|-V}
      +B^2(1+3/V)e^{-144}\right].
$$

I cut off the smoothed series at $N=4660355$. Write $p=(B^2/4)\log(N/X)>1$. For $n>N$, the inequality $\mathrm{erfc}(x)\le e^{-x^2}$ for $x\ge0$ and integral comparison bound the omitted sum by $\sqrt N\, e^{-p\log(N/X)}/(p-1/2)$. This gives an error below $1.51\times10^{-27}$ from truncation and below $0.0004090$ from the functional-equation approximation, at each endpoint. The resulting intervals for both signed beta values exclude zero.
