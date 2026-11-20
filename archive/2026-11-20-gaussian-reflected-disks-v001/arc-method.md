# Winding around the disk centered at 33/64

I tested the circle centered at $33/64+i(T_D-1/512)$ with radius $15/1024$.
The full Gaussian factor has unresolved winding. At each of four norm cutoffs,
the smoothed finite contribution has certified winding zero.

| Norm cutoff | Arcs for the finite winding | Finite winding | Real part of the finite contribution on the circle |
|---:|---:|---:|---|
| 16,384 | 64 | 0 | Strictly negative throughout |
| 65,536 | 512 | 0 | Positive at the easternmost point and negative at the southernmost |
| 262,144 | 64 | 0 | Strictly negative throughout |
| 1,048,576 | 64 | 0 | Strictly positive throughout |

Each bound includes the error from replacing the smoothed weights by 1 in
the stated finite range. At 65,536 the first 64-arc attempt did not establish
the finite winding. All the calculations, including the 512-arc refinement,
enclose zero on every arc after the omitted norms are included.

## Two series off the critical line

The archived conductor $Q$, real quadratic ideal character and Dottie height
give $B=\sqrt Q/(2\pi)$, $S=B^2|\Gamma(2+iT_D)|$, and
$f(s)=B^s\Gamma(s)L(s)/S$. Set $G(z)=\exp(z^2-i\pi z/2)$ and

$$
 I(s)=\frac1{2\pi i}\int_{(b-\Re s)}f(s+z)G(z)\frac{dz}{z},
 \qquad b=1+1/32 .
$$

The order-one entire completion, Gaussian weight, real ideal coefficients
and root-number $+1$ functional equation give
$f(s)=I(s)+\overline{I(1-\bar s)}$ by a contour shift.
The reflected integral replaces $G(z)$ by $G(-z)=\overline{G(\bar z)}$.
The Dirichlet series at $b$ converges absolutely. Write $I_{\le N}(s)$ and
$I_{>N}(s)$ for the two norm ranges. In the finite sum the individual
contours shift to $\Re(s+z)=a=1/16$, crossing the pole at $z=0$.
The intervening strip contains no gamma pole. The residue sum is
$B^s\Gamma(s)\sum_{n\le N}a_n n^{-s}/S$. Adding the reflected conjugate
of this expression gives the explicit prefix used in the interval calculation.

## Uniform bounds over both reflected circles

For $c=a$ or $b$, write $v=\Im s+u$.
Take $d_0=\min_{.46\le\sigma\le.54}|c-\sigma|$ and
$d_1=\max_{.46\le\sigma\le.54}|c-\sigma|$. Both $s$ and $1-\bar s$
stay within these real parts, with $t=\Im s\in[t_-,t_+]$ and
$t_\pm=T_D\pm1/32$. For $|u|\le20$ put

$$
 M_c=\exp\!\left(\frac{2|c-1/2|}{t_- -20}\right)
 \begin{cases}
 (t_- -20)^{c-1/2},&c<1/2,\\
 (t_+ +22)^{c-1/2},&c\ge1/2 .
 \end{cases}
$$

Then $|\Gamma(c+iv)|e^{\pi v/2}/\sqrt{2\pi}\le M_c$.
Integrate $\Re\psi(x+iv)$ from $1/2$ to $c$ and apply first-order
Euler summation, which gives
$|\psi(x+iv)-\log(x+iv)|\le (1/2+\pi/4)/|v|$ for $x>0$.
At $x=1/2$ use $|\Gamma(1/2+iv)|^2=\pi/\cosh(\pi v)$.
For every real $u$, including $|u|>20$, the same scaled gamma modulus
is at most $16(t_++1+|u|)$. Indeed the beta integral gives
$|\Gamma(c+iv)|\le\Gamma(c)|\Gamma(h+iv)|/\Gamma(h)$
with $h=1/2$ and $3/2$ for the lower and upper lines respectively.
The script bounds both constant ratios by 16. The half-integer gamma
formula and its recurrence give the stated estimate.

Use $|\Gamma(2+iT_D)|^2=\pi T_D(1+T_D^2)/\sinh(\pi T_D)$. The resulting
absolute bound for a single norm is

$$
 |a_n|n^{-c}
 \frac{B^{c-2}e^{\pi/64+d_1^2}}{2\pi d_0\sqrt{T_D(1+T_D^2)}}
 \left[\sqrt{\pi}M_c+
 16e^{-400}\left(\frac{t_++1}{20}+1\right)\right].
$$

The tilt in $G$ cancels the $u$-dependent exponential in the gamma
estimate. The remaining tails use
$\int_{20}^\infty e^{-u^2}du\le e^{-400}/40$ and
$\int_{20}^\infty u e^{-u^2}du=e^{-400}/2$.
At $a$, sum $|a_n|n^{-a}$ over the finite prefix.
At $b$, use $\sum|a_n|n^{-b}\le\zeta_{\mathbb Q(i)}(b)
=\zeta(b)\beta(b)\le\zeta(b)$ and subtract the explicit absolute prefix.
Double each bound to include both sums in the functional equation.

## Arithmetic on the closed arcs

The angle intervals $[2\pi j/K,2\pi(j+1)/K]$ cover the circle counterclockwise.
Every arc is evaluated with 192-bit ball arithmetic. For $s=s_0+d$,
$s_0=1/2+iT_D$, the gamma prefactor is its scaled value at $s_0$
times $\exp(d\log(iBT_D)+e)$, where $|e|\le 3|d|/(T_D-1)$.
Integrate the digamma estimate along the segment from $s_0$ and use
$|\log s-\log(iT_D)|\le |s-iT_D|/(T_D-1)$.
The finite Dirichlet polynomial is Taylor-expanded through degree 16 about
$s_0$. With $m=\sum_{n\le N}|a_n|n^{-1/2}$ and $x=|d|\log N$,
the remainder is at most $me^x x^{17}/17!$.

Each complex arc enclosure avoiding zero lies inside an open half-plane
through the origin. Its argument change is therefore the principal argument
of the endpoint ratio. The sum of these changes divided by $2\pi$ isolates
a unique integer for each resolved finite winding. The minimum certified
boundary modulus must exceed the finite weight-replacement error before
transferring that integer to the exact smoothed finite function.

At $N=262144$, the maximum real part of the exact smoothed finite function
is below $-7.6098\times10^{-29}$ on every arc. Thus a uniform upper
bound $\Re(\mathrm{omitted})<7.6098\times10^{-29}$ would put the whole
completed image strictly inside the left half-plane and certify zero winding.
The available absolute omitted-norm bound here is $2.312\times10^{-17}$.

## Reproduce

Run `python -B replay.py` as described in the [snapshot index](README.md). The five JSON records give the enclosure on each closed arc and the values at the four compass points.
