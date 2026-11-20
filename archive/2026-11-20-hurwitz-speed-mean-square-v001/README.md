# Mean squared speed of a Hurwitz zero at the shifts 1/3 and 2/3

I asked how fast a zero of my symmetrized Hurwitz reference moves when it passes through a simple Riemann zero. Liu’s real-part bound gave me an upper and a lower speed at every height. Here I compute the mean square in the three intervals selected by my Dottie orbit. The first two intervals can be distinguished even before using the positions of their zeros. I also derive a long-run mean, its first correction, and a short-window estimate at simple zeros. [Angular velocity and its derivation](../2026-11-20-liu-angular-velocity-v002/README.md) · [Liu, Theorem 1.1](https://hexagonmath.org/2611.00421v1)

The [two-input continuation](two-input-spectrum.md) pairs two evaluations at each identical determinant root. Five readings isolate the first nonreal radius and angle. Allowing two shifts in the speed average also gives an exact correlation involving $`\zeta(3+u+\bar v)`$.

Put $`\chi=\chi_{-3}`$, equal to $`1,-1,0`$ on $`1,2,0\bmod 3`$, and define

~~~math
Q(z)=\frac{L(1+z,\chi)}{1-3^{-z}},\qquad G(z)=\frac3\pi Q(z),\qquad f(t)=|G(1/2+it)|^2 .
~~~

If $`\rho`$ is a simple nontrivial zero of Riemann zeta, the normalized speed is $`S(\rho)=|G(\rho)|=|dw/da|\,|\zeta'(\rho)|/|\rho|`$ at either angle $`a=\pm\pi/6`$. Here $`a`$ is in radians. The two velocities have opposite signs. The arithmetic quantity $`|G(\rho)|^2`$ also has a value at a multiple zero. Every sum below identifies which zeros it counts. To convert any squared-speed result to a mean square of $`Q`$ itself, multiply it by $`\pi^2/9`$. [McPhedran, Botten and Nicorovici, equations (3.1) and (3.4)](https://doi.org/10.1098/rspa.2006.1763)

## Three short intervals with every zero counted

My period-640 orbit specifies $`T_D=4{,}526{,}119{,}322{,}477.945393\ldots`$. Earlier whole-strip counts isolate exactly 2, 5 and 4 zeros, each simple and on the critical line. The third column encloses the mean of $`S^2`$ at those zeros. The fourth encloses $`f(t)`$ at **every height** in the window using only its two endpoints. I used square brackets for inclusive, outward-rounded bounds. [Height, counts and Hardy brackets](../2026-11-20-liu-angular-velocity-v002/README.md#where-the-zero-locations-are-sharper) · [Individual enclosures and arithmetic checks](windows-and-means.json)

| Closed height interval | Zeros | Mean squared speed at the zeros | Range enclosing the entire vertical segment |
| --- | ---: | --- | --- |
| $`T_D\pm1/4`$ | 2 | [0.474901, 0.475146] | [0.413662, 0.643184] |
| $`2T_D\pm1/2`$ | 5 | [0.919283, 0.919755] | [0.798039, 1.069995] |
| $`3T_D\pm1/2`$ | 4 | [1.421718, 1.422448] | [0.696575, 2.179008] |

Because $`0.643184<0.798039`$, even the fastest permitted normalized motion in the first window is slower than the slowest permitted motion in the second. In the third window the individual squared speeds run from about $`0.851`$ to $`2.097`$. Pooling the eleven zeros with equal weight gives [1.021190, 1.021714]. The full-segment calculation uses the previously certified real part $`1/2`$ and needs no individual zero ordinates. [Replay](verify_moments.py)

I also evaluated the proposed estimator $`f(t)`$ at the three window centers. It gives **[0.483299, 0.483548]**, **[0.963583, 0.964078]** and **[1.035278, 1.035810]**, in order. The mean at the actual zeros is lower than the center by about 0.0084 and 0.0443 in the first two windows. In the third it is **higher by [0.385908, 0.387169]**. That window has the same width as the second. The four zero ordinates and the variation of $`f`$ across them matter there.

## Two constants for the sum over all zeros

Write $`N(T)`$ for the number of zeros $`\rho=\beta+i\gamma`$ with $`0<\gamma\le T`$, counted with multiplicity. My two-term estimate is

~~~math
\frac1{N(T)}\sum_{0<\gamma\le T}|G(\rho)|^2
 =D-\frac{T}{2\pi N(T)}K+O\!\left(\frac1{\log^2 T}\right),
\quad
D=\frac{13\zeta(3)}{\pi^2},\qquad
K=D\left(\log 3-2\frac{L'(2,\chi)}{L(2,\chi)}\right).
~~~

Here $`D=1.58331976703645\ldots`$ and $`K=1.19273804344757\ldots`$. The correction is negative and of order $`1/\log T`$. Consequently the cumulative mean approaches $`D`$ from below for all sufficiently large $`T`$. For the quotient as originally posed, the limiting mean square is $`13\zeta(3)/9=1.73630441567496\ldots`$. The proof uses Liu’s strip, the Landau–Gonek explicit formula, and Selberg’s zero-density estimate. [Gonek, Theorem 1](https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf) · [Ford and Zaharescu, Lemma 2, quoting Selberg](https://arxiv.org/pdf/math/0405459)

| First zeros, through $`T=\gamma_n`$ | Measured mean of $`S^2`$ | Two terms $`D-KT/(2\pi n)`$ |
| ---: | ---: | ---: |
| 64 | 1.160365 | 1.079345 |
| 256 | 1.248759 | 1.228173 |
| 1,024 | 1.326768 | 1.315032 |

These finite comparisons use the coefficients derived below. FLINT isolated the zeros and checked $`\zeta'(\rho)\ne0`$ for all 1,024. The table rounds each value to six decimals. [Directed enclosures](windows-and-means.json)

### Reflection in a finite height interval

Write $`\rho^\sharp=1-\bar\rho`$, the zero at the same height reflected about $`\Re w=1/2`$. In any height interval $`I`$ with $`M>0`$ zeros counted with multiplicity, the two lists $`\rho`$ and $`\rho^\sharp`$ differ by a permutation. The real Dirichlet coefficients give $`G(1-\rho)=\overline{G(\rho^\sharp)}`$. Expanding the squared difference and summing proves

~~~math
\frac1M\sum_I |G(\rho)|^2
 =\frac1M\Re\sum_I G(\rho)G(1-\rho)
  +\underbrace{\frac1{2M}\sum_I|G(\rho)-G(\rho^\sharp)|^2}_{E_I\ge0}.
~~~

Every critical-line zero contributes zero to $`E_I`$. For an off-line pair the summand measures the difference between the two arithmetic values. Equality of those values would also give zero. The three certified Dottie windows have $`E_I=0`$ exactly. Lean verifies the finite permutation identity, its inequality, and the pointwise equality condition. [Lean proof](../../lean/SuperZeta/Oriented/HurwitzSpeedMoment.lean) · [Riemann zero symmetries](https://dlmf.nist.gov/25.10.i)

### The diagonal and the prime powers

Write each $`n=3^j m`$ with $`3\nmid m`$, and put $`a_n=\chi(m)/m`$. Multiplying the Dirichlet series for $`L(1+z,\chi)`$ by the geometric series at three gives $`Q(z)=\sum_{n\ge1}a_n n^{-z}`$ for $`\Re z>0`$. The coefficients are real and completely multiplicative, with $`a_3=1`$ and $`a_p=\chi(p)/p`$ at every other prime. In the product $`G(\rho)G(1-\rho)`$ the $`(n,m)`$ term is $`(3/\pi)^2a_na_m(m/n)^\rho/m`$. Terms with $`m=n`$ contribute

~~~math
D=\frac9{\pi^2}\sum_n\frac{a_n^2}{n}
  =\frac9{\pi^2}\left(\sum_{j\ge0}3^{-j}\right)
       \left(\sum_{3\nmid m}m^{-3}\right)
  =\frac{13\zeta(3)}{\pi^2}.
~~~

For $`x>1`$, Landau’s formula gives $`\sum_{0<\gamma\le T}x^\rho=-(T/2\pi)\Lambda(x)+O_x(\log T)`$, with $`\Lambda(x)=\log p`$ when $`x=p^k`$ and zero otherwise. For $`0<x<1`$ the sum is $`x`$ times the conjugate of the sum at $`1/x`$, by reflection of the zero list. Thus the two orders of $`(n,np^k)`$ give equal real contributions. Summing their coefficients gives

~~~math
K=2D\sum_p\sum_{k\ge1}\frac{a_p^k\log p}{p^k}
 =2D\left(\frac{\log3}{2}
       +\sum_{p\ne3}\frac{\chi(p)\log p}{p^2-\chi(p)}\right).
~~~

The index $`p`$ runs over primes and $`k`$ over positive integers. The second sum is $`-L'(2,\chi)/L(2,\chi)`$. The verifier compares this differentiation with a finite prime sum and a rigorous bound on its tail. In particular it checks the sign of $`K`$. [Gonek, equations (1)–(3)](https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf) · [Dirichlet Euler product](https://dlmf.nist.gov/25.15.E2)

### Controlling the errors

Liu’s result and reflection allow $`b=1/8\le\beta\le1-b`$. Put $`\eta=1/16`$. Throughout this strip, truncating $`Q`$ at $`n\le Y`$ costs at most $`Y^{-\eta}\sum_n |a_n|n^{-b+\eta}`$. This sum converges by the decomposition $`n=3^j m`$. The same bound applies at $`1-\rho`$. The tails of the diagonal and prime-power constants are $`O(Y^{-\eta})`$ as well. For the prime-power tail use $`1_{np^k>Y}\le(np^k/Y)^\eta`$. The resulting product of $`\sum_n a_n^2 n^{-1+\eta}`$ and $`\sum_{p,k}|a_p|^k\log p\,p^{-k(1-\eta)}`$ converges.

For a ratio $`1<x=m/n\le Y`$ with $`m,n\le Y`$, its distance from every unequal integer prime power is at least $`1/Y`$, and $`\log x\ge 1/Y`$. Gonek’s uniform Theorem 1 therefore bounds the remainder per ratio by $`O(Y^2\log^2(2T))`$ for $`2\le Y\le T`$. There are at most $`Y^2`$ terms, each with bounded coefficient. Taking $`Y=\lfloor T^{1/10}\rfloor`$ gives
$`\Re\sum G(\rho)G(1-\rho)=DN(T)-KT/(2\pi)+O(T^{1-c})`$ for some $`c>0`$.

To bound the squared differences, $`G'`$ is uniformly bounded on Liu’s strip by absolute convergence of the logarithmically weighted series. Hence $`|G(\rho)-G(\rho^\sharp)|\ll|\beta-1/2|`$. Selberg’s bound, including reflection, gives $`\#\{0<\gamma\le T:|\beta-1/2|\ge u\}\ll T\log T\,e^{-u\log T/4}`$ for $`0<u\le1/2`$. Integrating against $`2u\,du`$ gives $`\sum|\beta-1/2|^2\ll T/\log T`$. Dividing by $`N(T)\asymp T\log T`$ gives $`E_{(0,T]}=O((\log T)^{-2})`$ and proves the two-term estimate. [Selberg’s uniform density bound, Lemma 2](https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf) · [Zero-counting asymptotic](https://dlmf.nist.gov/25.10.i)

The reflection identity also gives a local consequence at arbitrary large heights. For every $`H=H(T)\to\infty`$ with $`H\le T`$, the mean over $`T<\gamma\le T+H`$ is $`D+E_I+o(1)`$. Indeed, for any fixed ratio other than one, the difference of the two Landau sums is $`O_x(H+\log T)`$, while $`M\sim(H/2\pi)\log T`$ by the Riemann–von Mangoldt formula. First truncate at fixed $`Y`$, then let $`Y\to\infty`$ using the uniform tails above. In particular the lower limit of these multiplicity-weighted means is at least $`D`$ even when the window grows very slowly.

### The first correction in growing height intervals

For multiplicity-weighted sums the prime-power correction can already be resolved in many growing short windows. Fix $`\varepsilon>0`$ and a length $`X^\varepsilon\le H=H(X)\le X`$. For $`I=(t,t+H]`$, $`t\in[X,2X]`$, repeating the truncation with $`Y=\lfloor H^{1/10}\rfloor`$ in the difference of the two Landau sums gives
$`M^{-1}\sum_I |G(\rho)|^2=D-KH/(2\pi M)+E_I+O_\varepsilon(X^{-c_\varepsilon})`$ for some $`c_\varepsilon>0`$, uniformly in $`t`$. Here $`M\asymp H\log X`$. Integrating $`E_I`$ over the center variable counts each squared horizontal displacement for a length at most $`H`$. The preceding Selberg estimate gives $`X^{-1}\int_X^{2X}E_I\,dt\ll(\log X)^{-2}`$. Outside a fraction $`O((\log X)^{-1/2})`$ of these intervals, the full error after the first two terms is consequently $`O_\varepsilon((\log X)^{-3/2})`$.

## The short-window estimate for simple zeros

Here I keep only the simple zeros, each counted once. The height-dependent quantity that estimates their mean square is $`f(t)`$ at the **center of the window**. Both the width and the permitted horizontal displacement enter the error.

**Proposition.** Let $`X`$ be sufficiently large, $`0<h\le1`$ the half-width and $`t\in[X,2X]`$. Outside a set of centers of length $`O(hX/(\log X)^2)`$, every nonempty sample of simple zeros with $`|\gamma-t|\le h`$ satisfies

~~~math
\left|\frac1{M_s}\sum_{\substack{|\gamma-t|\le h\\\rho\ {\rm simple}}} S(\rho)^2-f(t)\right|
 \le L_b\left(h+\frac{12\log\log X}{\log X}\right),
\qquad
L_b=2(3/\pi)^2 A(b)\bigl(-A'(b)\bigr),
~~~

where $`M_s`$ is the number of simple zeros in the window and $`A(b)=\sum |a_n|n^{-b}=(1-3^{-1-b})\zeta(1+b)/(1-3^{-b})`$. In particular the error tends to zero for shrinking half-widths $`h=h(X)\to0`$. The computable function $`f(t)`$ uses the height alone. It can be evaluated before finding any individual zero.

**Proof.** Absolute convergence gives $`|G|\le(3/\pi)A(b)`$ and $`|G'|\le(3/\pi)(-A'(b))`$ throughout the strip. Integrating along a segment shows that $`|G|^2`$ has Lipschitz constant $`L_b`$ there. With $`u_X=12\log\log X/\log X`$, the density estimate bounds the number of zeros up to $`3X`$ outside $`|\beta-1/2|<u_X`$ by $`O(X/(\log X)^2)`$. Each exceptional zero can affect at most $`2h`$ of center heights. At every remaining center, every zero in the window is within $`h+u_X`$ of $`1/2+it`$. Apply the Lipschitz estimate to each simple zero and average.

One can also center the window on a simple zero so that the sample always exists. Each exceptional zero can affect at most $`O(\log X)`$ such centers by the unit-interval zero-count bound. Hence at most $`O(X/\log X)`$ simple centers in $`[X,2X]`$ are exceptional. Alpöge and Furman’s Theorem A gives $`\gg X\log X`$ simple centers in that dyadic interval. The fraction excluded is $`O((\log X)^{-2})`$. At the three Dottie heights I used the sharper direct Euler-product enclosures in the table. [Alpöge and Furman, Theorem A](https://arxiv.org/html/2608.13637v2) · [Zero density](https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf)

### A cumulative bound when only simple zeros are counted

Let $`A_s(T)`$ be the mean of $`S^2`$ over the simple zeros up to $`T`$. Applying the diagonal calculation to $`1/G`$ gives its all-zero inverse second moment
$`B=(\pi/3)^2(1+1/3)\prod_{p\ne3}(1+p^{-3})=\pi^2\zeta(3)/(7\zeta(6))`$.
Indeed, the inverse Euler factors are polynomials of degree one. The absolute series and derivative converge uniformly in Liu’s strip. Fixed truncation, Landau’s formula, and the same reflection estimate therefore give the limit $`B`$.

For any lower bound $`\kappa`$ on the limiting inferior fraction of simple zeros, positivity gives $`\limsup A_s(T)\le D/\kappa`$. Cauchy–Schwarz on the simple zeros gives $`\liminf A_s(T)\ge\kappa/B`$: the simple count squared is bounded by their squared-speed sum times their inverse-squared-speed sum, and the last sum is at most the all-zero inverse sum. Taking $`\kappa=2/3`$ gives

~~~math
0.40017452 < \frac{2/3}{B} \le \liminf A_s(T)
 \le \limsup A_s(T) \le \frac{D}{2/3} < 2.37497966 .
~~~

~~Can I bound the mean square over simple zeros in a short interval and compute it for the Dottie windows?~~ The short-window proposition and the three certified counts answer this. **Open.** Does the cumulative mean restricted to simple zeros have the same limit $`D`$ and the same first correction as the multiplicity-weighted mean? A formula for how simplicity weights the prime-power ratios in Landau’s sum would address the second coefficient. Laaksonen and Petridis study related discrete moments of shifted Dirichlet $`L`$-values in a different range of shifts. [Their paper, §1](https://discovery.ucl.ac.uk/id/eprint/1544001/1/lvalues_accepted.pdf)

## Numerical and formal verification

I used Python 3.12.11, python-flint 0.9.0 (FLINT 3.6.0), and 160-bit ball arithmetic. The input is the [immutable rational bracket file](../2026-11-20-liu-angular-velocity-v002/windows.json). At each bracket I multiplied the Euler factors through prime cutoff $`P=10^6`$. For $`U_P=\zeta(3/2)\prod_{p\le P}(1-p^{-3/2})`$, the squared modulus of the omitted product is in $`[U_P^{-2},U_P^2]`$. The factor at three uses $`3^{-1/2}`$ in $`Q`$ and is evaluated explicitly. A separate sum of the first 65,536 terms of $`L(3/2+it,\chi)`$, with absolute tail at most $`2/\sqrt{65{,}536}`$, overlaps every prime-product enclosure. To cover whole windows, I used 48 closed subintervals per window, prime cutoff 2,000 and the same tail proof. All interval claims include the uncertainty in height. The code also checks the sign of $`K`$ two ways, via the Dirichlet derivative and a prime sum with tail bounded by $`(\log P+1)/(P(1-P^{-2}))`$ before scaling.

Lean checks the reflection algebra for the scaled Dirichlet quotient, and the evaluation of the diagonal in terms of the geometric series at three and the two Hurwitz residue classes. The contour counts are prior FLINT certificates. The estimates using Gonek and Selberg are written analytic proofs. The script, note and Lean statements are original to this deposit, extending the [reviewed angular-velocity note](../2026-11-20-liu-angular-velocity-v002/README.md). [Verification source](verify_moments.py) · [Numerical record](windows-and-means.json) · [Lean scope](../../lean/SuperZeta/Oriented/HurwitzSpeedMoment.lean) · [File hashes](manifest.json)

From the repository root run

~~~sh
python archive/2026-11-20-hurwitz-speed-mean-square-v001/verify_moments.py
python tools/check_lean.py
~~~

