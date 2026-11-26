# The centered Gaussian prime ramp from one to two million

I used the same 101 sample points and evaluated the actual signed ramp, including its affine center. A 160-bit Arb replay gives

$$
152<F(x)<954,\qquad
0<F(x)<0.933\sqrt{x},\qquad 10^6\le x\le2\cdot10^6.
$$

The bounds use the quartic's own coefficients. Lean checks the identities connecting the folded Gaussian integral, the center and the original ramp. The numerical enclosure uses Arb arithmetic and the written error bounds below. Lean checks the integer comparisons on the rounded table and carries the tables of enclosures to the whole interval. [Lean center](GaussianPrimeCenter.lean) · [Lean interval theorem](GaussianPrimeCenterWindow.lean) · [Independent replay and axioms](gaussian-prime-center-audit.txt) · [Numerical verifier](replay-gaussian-prime-center.py) · [All 101 sample enclosures](gaussian-prime-center-results.json)

## The constant in the ramp

Write $C=\sqrt{26509772707289}/\pi$, $\Lambda(w)=C^w\Gamma(w)G(w)$ and $\Theta(v)=\sum_{n\ge1}B(n)e^{-nv}$ for the archived theta reading. Reflection gives $\Theta(t/C)=t^{-1}\Theta(1/(tC))$. For the value and slope at one, this gives

$$
\begin{aligned}
\Lambda(1)&=\int_1^\infty \Theta(t/C)(1+t^{-1})\,dt,\\
\Lambda'(1)&=\int_1^\infty \Theta(t/C)(1-t^{-1})\log t\,dt.
\end{aligned}
$$

In the slope integral, inversion contributes $\log(1/t)=-\log t$. The two readings in the numerator and denominator therefore have different weights. Lean uses Mellin differentiation and the checked theta reflection for both. Removing the completion gives

$$
c_0=\frac{\Lambda'(1)}{\Lambda(1)}-\log C+\gamma_{\mathrm E}+Q,\qquad
Q=\sum_{p}\sum_{k\ge2}\frac{a(p^k)\log p}{p^k}.
$$

Here $a(p^k)$ is the actual weight in $-G'/G$. This is the same $c_0$ in $F(x)=c_0x+\sum_{p<x}a(p)\log p\,(x/p-1)$. The sum in the Lean statement is over all integers up to the cutoff with a zero coefficient at nonprimes. [Previous centering argument](gaussian-prime-classes.md#the-exact-signed-estimate-to-carry-over) · [Prime-only ramp](GaussianPrimeOnlyWindow.lean)

## Bounding the two integral readings

I generated the coefficients through $N=2^{25}$ from the local Euler polynomials. I checked the split-prime traces and determinants against independent evaluations on the two Gaussian generators. This checks 1,031,645 split labels. The inert norms through $N$ give 387 additional checks. A separate quarter-lattice enumeration agrees through norm 10,000. [Actual split prime coefficient](GaussianPrimeSupport.lean)

In each block $l\le n\le l+\lfloor l/16\rfloor$, I kept 13 exact integer moments $\sum_n B(n)(n-l)^j$ for $0\le j<13$. With $y=l/C$ and $J=13$, integrating the finite Taylor expansion for $e^{-tn/C}$ against $t^{w-1}$ gives the block reading

$$
\sum_{j=0}^{J-1}
\frac{(-1)^j}{j!\,l^j}
\left(\sum_n B(n)(n-l)^j\right)y^{-w}\Gamma(w+j,y).
$$

I add the same expression with $w$ replaced by $1-w$. The absolute Taylor remainder in the exponential is bounded by $e^{-yt}(yt/16)^J/J!$. Since $|B(n)|\le d(n)$ from the local factors, $\sum_{n\le N}|B(n)|/n\le(1+\log N)^2$. Write $B_0=(17/16)C(1+\log N)^2/16^J$. Substituting $z=yt$ in the remainder gives a total error at most $2B_0$ for the value and $B_0(\log C+J+1)$ for the imaginary part at $w=1+ih$ divided by $h$. The latter bound uses $|\sin(h\log t)|\le h\log t$ and $\log t\le\log C+z$.

For the omitted norms let $S=\sum_{n>N}d(n)e^{-n/C}$. In a block $v<n\le u=v+H$, every divisor pair has a member at most $\sqrt u$. There are at most $H/a+1$ multiples of $a$ in the block, so its divisor mass is at most $2H+H\log u+2\sqrt u$. I use $H=2^{21}$, $u_0=N+H$, and $q=e^{-H/C}$. The concave functions $\log u,\sqrt u$ are bounded above by their tangents at $u_0$. Summing the resulting geometric series gives

$$
S\le e^{-N/C}\left(
\frac{2H+H\log u_0+2\sqrt{u_0}}{1-q}
+\left(\frac{H^2}{u_0}+\frac{H}{\sqrt{u_0}}\right)\frac{q}{(1-q)^2}
\right).
$$

The value tail is at most $2(C/N)S$. The slope tail is at most $(C/N)^2 S$, by $\log t\le t-1$. I compute the slope as $\Im\Lambda(1+ih)/h$ with $h=2^{-28}$. Since $|\sin v-v|\le |v|^3/6$, the error from this step is at most $h^2/6$ times the absolute third log moment. For the retained norms it is bounded by

$$
C(1+\log N)^2\left((\log C)^3+3(\log C)^2+6\log C+6\right).
$$

This follows from $\log t\le\log C+nt/C$ and the first four exponential moments. The omitted norms contribute at most $6(C/N)^4S$ using $\log^3t\le(t-1)^3$. The resulting errors added to the finite Arb readings are below $0.007074$ for the value and $0.000182$ for the slope.

## Putting the center into all 101 readings

I sum the higher prime powers as geometric series at each rational prime up to eight million. For a split prime with marked signs $u,v$, the local contribution to $Q$ is $(\log p)/p$ times $u^2/(p-u)+v^2/(p-v)$. An inert prime with sign $e$ above norm $p^2$ contributes $2(\log p)e/(p^2-e)$. At two the contribution is $(\log 2)/2$. The absolute contribution of each prime is at most $2\log p/[p(p-1)]$. Beyond the cutoff $P$ I sum over all integers and use the decreasing integral of $\log t/t^2$. This gives an error at most $2(\log P+1)/(P-1)<0.000004224$. The resulting enclosure gives $-0.857455<c_0<-0.857445$.

I use the exact chord identity to extend the sample enclosures across their cells. Negative slope jumps bound the increase from the chord, and positive jumps bound the decrease by the same argument. The recorded interval for each endpoint includes the uncertainty in $c_0$. Using both allowances gives a lower bound greater than 152 and an upper bound less than 954. Dividing each cell's upper absolute bound by the square root of its left endpoint gives a maximum upper estimate less than $0.933$. [Lean chord identity and one-sided error](GaussianPrimeMesh.lean)

The verifier rounds the two endpoint values and the two error allowances outward to integer hundredths. The 160-bit run and a 192-bit replay give identical tables. Lean checks the squared inequality for the upper bound and the comparisons with 152 and 954 in every row. The theorem takes the association of those rational bounds with the actual sample values and slope masses as the explicit premise `ArchivedPrimeMeshEnclosures`. [Exact theorem and premise](gaussian-prime-center-audit.txt)

The field implication uses sample bounds with fixed constants on cofinal windows for each exponent above one half. The measured window gives an actual signed example of that input at the square-root scale.

```bash
python replay-gaussian-prime-center.py --output gaussian-prime-center-results.json
```
