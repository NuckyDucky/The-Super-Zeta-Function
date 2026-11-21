# Six smoothed Gaussian bands and the upper tail

Put $T=T_D$, $B=\sqrt Q/(2\pi)$, $S=B^2|\Gamma(2+iT)|$ and $K=BT$. The positive-height contribution is paired with its conjugate at $1-\bar s$. The rectangle estimates use the same smoothing $\lambda=1$ on both sides. The unit factor $e^{-i\pi x/2}$ below was used in the original reading at one angle. The rectangle calculation in [retained.py](retained.py) evaluates the two terms before that rotation.

## Enclosing each smoothed contribution

Use $G(z)=e^{z^2-i\pi z/2}$, $P(s)=B^s\Gamma(s)/S$ and $s^*=1-\bar s$. The exact contribution is

$$
v_n=e^{-i\pi x/2} a_n
\bigl(P(s)n^{-s}V(s,n)+\overline{P(s^*)n^{-s^*}V(s^*,n)}\bigr),
$$

where

$$
V(s,n)=\frac1{2\pi i}\int_{\Re z=1}
\frac{\Gamma(s+z)}{\Gamma(s)}(B/n)^z e^{z^2-i\pi z/2}\frac{dz}{z}.
$$

This contour is absolutely convergent, and summing it with the reflected contour gives the complete Gaussian factor. This choice of smoothing is allowed for the full equation. The results here pertain to this specified weighting of individual norms. The earlier optimized transverse bound used a different smoothing parameter.

For $\ell=\log(B/n)+\log s-i\pi/2$ and $\Phi(\ell)=\tfrac12\operatorname{erfc}(-\ell/2)$, the replay evaluates

$$
V(s,n)=\Phi(\ell)+\frac{\Phi''(\ell)-\Phi'(\ell)}{2s}+E(s,n),
\qquad |E(s,n)|\le 4000/T_D^2+10^{-100}.
$$

Here $\Re s\in[0.46,0.54]$, $|\Im s-T_D|<1/16$, $K/n<5$, and $T_D>4\times10^{12}$. With $z=1+iu$, first take $|u|\le20$. One Euler–Maclaurin step, with the periodic second Bernoulli polynomial bounded by $1/6$, gives for $\Re v>0$

$$
\left|\psi(v)-\log v+\frac{1}{2v}\right|
\le \frac{1}{12|v|^2}+\frac16\int_0^\infty\frac{dy}{|v+y|^3}
\le\frac{1}{4(\Im v)^2}.
$$

Integrate along $v=s+\tau z$, $0\le\tau\le1$. On this segment $|v|>T_D-21$. Expanding $\log(s+\tau z)$ through its linear term and $(s+\tau z)^{-1}$ through its constant gives

$$
\left|\log\Gamma(s+z)-\log\Gamma(s)-z\log s-\frac{z^2-z}{2s}\right|
\le\frac{6|z|(1+|z|)^2}{T_D^2}.
$$

Since $|z|<21$, exponentiation bounds the error when replacing $\Gamma(s+z)/(\Gamma(s)s^z)$ by $1+(z^2-z)/(2s)$ by $16(1+|z|)^4/T_D^2$. The integral of the discarded term is bounded using $|z|\ge1$, $e^{\Re(z^2)}=e^{1-u^2}$, and $|(B/n)^zs^ze^{-i\pi z/2}|\le1.01 K/n$. The last inequality follows from $|\arg s-\pi/2|<1/T_D$. The remaining integral satisfies

$$
\int_{\mathbb R}(2+|u|)^4 e^{-u^2}\,du
=\tfrac{115}{4}\sqrt\pi+40<92.
$$

These estimates give $4000/T_D^2$. For the complementary range $|u|>20$, the beta integral compares $|\Gamma(\Re s+1+i(\Im s+u))|$ to $|\Gamma(5/2+i(\Im s+u))|$ with ratio bounded by $\Gamma(\Re s+1)/\Gamma(5/2)<1$. The half-integer gamma identity and recurrence bound its scaled magnitude by $\sqrt{2\pi}(|\Im s+u|+2)^2$. The denominator satisfies $|\Gamma(s)|e^{\pi\Im s/2}>1/10$, by integrating the preceding digamma bound horizontally from $1/2+i\Im s$. Hence the true-weight tail is bounded by integrating $30(B/n)e(T_D+|u|+3)^2 e^{-u^2}/(2\pi)$ on $|u|>20$. The approximating weight uses the smaller majorant $5.1e(1+(1+|u|)^2/T_D)e^{-u^2+|u|/T_D}$. Their sum is below $10^{-100}$ at the recorded height. Integrating the main term gives $\Phi$ by Gaussian inversion. Differentiating in $\ell$ gives the indicated derivatives. Directed complex-ball arithmetic includes this weight error for each nonzero coefficient.

## Summing one norm band for a continuum of inputs

Let $s_0=1/2+iT_D$, $s=s_0+z$, and write $V(s,n)$ for the smoothed weight. For each band use its integer midpoint $h$ and calculate in directed ball arithmetic

$$
C_h=\sum_n a_n e^{-iT_D\log(n/h)},\quad M_h=\sum_n |a_n|,
\quad L=\max_n|\log(n/h)|.
$$

On both pieces of the smoothed equation and on the small derivative neighborhoods used below, $|s-iT_D|<1$, $L<10^{-12}$. After taking out $P(s)h^{-s}$, the positive-height piece of the sum differs from $C_h V(s,h)$ by at most $M_h(4L+4E)$, where $E=4000/T_D^2+10^{-100}$. To check this estimate set $l=\log(n/h)$ and factor the summand as $a_n e^{-iT_D l}\,e^{-(s-iT_D)l} V(s,n)$. The first exponential fixes the arithmetic phase at the actual Dottie height. By the established smoothing estimate, $V$ differs by at most $E$ from

$$
A(\ell)=\Phi(\ell)+\frac{(-\ell/2-1)\Phi'(\ell)}{2s},\quad
\Phi(\ell)=\tfrac12\operatorname{erfc}(-\ell/2),\quad
\ell=\log(B/n)+\log(s)-i\pi/2.
$$

In these bands $|\Re\ell|<1.4$, $|\Im\ell|<10^{-12}$. From $\Phi'=e^{-\ell^2/4}/(2\sqrt\pi)$ and $\Phi''=-\ell\Phi'/2$ one obtains $|A|<1.01$, $|A'|<0.3$. For the bound on $\Phi$, integrate its derivative along the vertical segment from the real axis, where $0<\Phi<1$. The change from multiplying by $e^{-(s-iT_D)l}$ is bounded by $1.01e^L L$. The change in $A$ is bounded by $0.3L$. Including the weight error at both norms gives a bound below $4L+4E$ for each signed summand of unit magnitude. All coefficient hashes match the earlier direct norm-by-norm computations. All six evaluations at $537\pi/512$ overlap the old direct sums.

For each input interval the prefactor is evaluated as $P(s_0)h^{-s_0}\exp(z(\log(BT_D/h)+i\pi/2)+e_\Gamma)$. The existing gamma enclosure bounds $|e_\Gamma|$ by $3|z|/(T_D-1)$; its implementation permits a complex square of this radius in each component. The reflected piece is taken at $-\bar z$, conjugated, and added in the same completion. This construction preserves the argument of the reference and the smoothing phase.

## The shifted sums

Take $G_\lambda(z)=\exp(\lambda z^2-i\pi z/2)$. The archived entire completion and functional equation give $F(s)=\sum_{n\ge1} H_{n,\lambda}(s)$ by the [two reflected contour integrals](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/bcea71d24671fbf81c9479ce31db1bad78f77ac1/archive/2026-11-20-gaussian-reflected-disks-v001/arc-method.md). The first term of $H_{n,\lambda}$ is

$$
\frac{a_n}{2\pi i S}\int_{(b-\sigma)}
      (B/n)^{s+z}\Gamma(s+z)G_\lambda(z)\frac{dz}{z},\qquad b>1.
$$

The second is the complex conjugate of this integral evaluated at $1-\bar s$. All the bounds below allow both terms. The integral can be moved right because of the Gaussian decay on vertical lines. Moving left for a finite set of norms also uses the residue theorem at all the poles crossed. No limits of the unsmoothed Dirichlet series in the critical strip are used.

For $0<\sigma<1$ the beta integral and the exact modulus of $\Gamma(1+iv)$ imply

$$
|\Gamma(\sigma+iv)|\le\Gamma(\sigma)|\Gamma(1+iv)|
 \le3\sqrt{1+2\pi|v|}\,e^{-\pi|v|/2}.
$$

Here $\Gamma(\sigma)\le 1/\sigma+e^{-1}<3$ on the two disks, by splitting the defining real integral at 1. The square-root bound follows from $y/(1-e^{-y})\le1+y$ for $y=2\pi|v|$. Also

$$
1/S \le \frac{e^{\pi T/2}}{B^2\sqrt{2\pi T(1+T^2)}}.
$$

Throughout, put $v=t+u$. The exponentials from the gamma bound and the tilt satisfy $e^{\pi T/2-\pi|v|/2+\pi u/2}\le e^{\pi\eta/2}$ even when $v$ is negative. The remaining factor $\sqrt{1+2\pi|v|}$ is bounded by $\sqrt{1+2\pi(T+\eta)}e^{|u|/(2T)}$. The number of Gaussian ideals of norm up to $Y\ge1$ is at most $2Y$, by counting their unique representatives $a+bi$, $1\le a\le\sqrt Y$ and $0\le b\le\sqrt Y$. Therefore $\sum_{n\le Y}|a_n|\le2Y$. [Gamma recurrence and special values](https://dlmf.nist.gov/5.4) · [Beta integral](https://dlmf.nist.gov/5.12)

## Uniform upper tail, including arbitrarily large norms

Move the first integral to $\Re z=k$ for a positive integer $k$. By recurrence the ratio of the absolute gamma values at $\sigma+k+iv$ and $\sigma+iv$ is the product of $k$ factors. Each factor at $j=0,\ldots,k-1$ satisfies

$$
|\sigma+j+iv|\le \sqrt{(\sigma+j)^2+(T+\eta)^2}+|u|
\le T\exp\left(\frac{\eta+|u|}{T}+\frac{(j+1)^2}{2T^2}\right).
$$

For the last inequality one may use $\sqrt{r^2+c^2}\le r+c^2/(2r)$, then $1+x\le e^x$. Partial summation of the ideal count gives $\sum_{n>X}|a_n|n^{-s'}\le2s'X^{1-s'}/(s'-1)$ for $s'=k+\sigma>1$. Both $s'/(s'-1)$ and $(B/X)^\sigma$ are largest at $\sigma_-$ for $X>B$. Write

$$
C(Y,k,\lambda)=\frac{24}{2\pi k}\sqrt{\frac\pi\lambda}\,
 \frac{Y(B/Y)^{\sigma_-}\sqrt{1+2\pi(T+\eta)}}{B^2\sqrt{2\pi T(1+T^2)}} .
$$

Using $1/|z|\le1/k$ and $\int_{\mathbb R}e^{-\lambda u^2+d|u|}\,du\le2\sqrt{\pi/\lambda}\,e^{d^2/(4\lambda)}$ gives the following bound for both reflected pieces together:

$$
\left|\sum_{n>X}H_{n,\lambda}(s)\right|
\le C(X,k,\lambda)\frac{k+\sigma_-}{k+\sigma_--1}
 \left(\frac KX\right)^k
 \exp\left(\frac{\pi\eta}{2}+\lambda k^2+\frac{k\eta}{T}
 +\frac{k(k+1)(2k+1)}{12T^2}
 +\frac{(k+1/2)^2}{4\lambda T^2}\right).
$$



For the six-band zero certificate, the replay takes $k=8$, $X=\lceil e^{17}BT\rceil$, $\eta=35/2048+1/8192$ and $\sigma_-=1/2-63/2048-1/8192$. The padding gives a circle of radius $1/8192$ about each point of the original rectangle for the Cauchy derivative bound. [Certificate and replay](README.md)
