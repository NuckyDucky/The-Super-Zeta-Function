# Replacing the smooth Gaussian weights on the measured norms

The signed blocks use weight one. The full equation uses a smooth weight on each of the two reflected terms. I bound their difference on the whole Dottie rectangle before comparing derivatives. For every fixed selection of norms through $360{,}710{,}144$, replacing the weight changes the horizontal derivative by less than $4.0\times10^{-47}S_0$. This includes every consecutive block and each of its partial prefixes. The bound through $2^{30}$ is $2.67\times10^{-41}S_0$.

| Upper norm $L$ | Left shift $k$ | Bound on the value divided by $S_0$, on the enlarged rectangle | Bound on the derivative divided by $S_0$, on the original rectangle |
| ---: | ---: | ---: | ---: |
| 360,710,144 | 12 | $4.865\times10^{-51}$ | $3.986\times10^{-47}$ |
| 1,073,741,824 | 11 | $3.250\times10^{-45}$ | $2.663\times10^{-41}$ |

The arithmetic below uses the smaller denominator $1.70\times10^{-29}$. The reference $S_0$ is the modulus of the completed weight-one sum through norm $276{,}824{,}064$ at $1/2+i(T_D-1/512)$. Its enclosure is $1.7047996314456\times10^{-29}$ with radius below $6.2\times10^{-43}$. To reproduce the two bounds, run `python -B tools/gaussian_prefix_smoothing.py`. [Directed-arithmetic calculation](../../tools/gaussian_prefix_smoothing.py)

## The two weight choices

Write $T=T_D$, $B=\sqrt Q/(2\pi)$, $S=B^2|\Gamma(2+iT)|$, and $a_n$ for the sum of my quartic character over Gaussian ideals of norm $n$. At $s=\sigma+it$ the smooth contribution from one norm on the positive-height side is

$$
\frac{a_n}{2\pi i\,S}\int_{(b-\sigma)}
       (B/n)^{s+z}\Gamma(s+z)\exp(z^2-i\pi z/2)\frac{dz}{z},
\qquad b>1.
$$

Add its complex conjugate evaluated at $1-\bar s$. Replacing the smooth weight by one means retaining the residue at $z=0$ in both integrals. The difference for a fixed set of norms is holomorphic on the measuring rectangle. [The archived smoothed functional equation](../../archive/2026-11-20-gaussian-reflected-disks-v001/arc-method.md)

Use coordinates $s=1/2+x+i(T+y)$. The rectangle has $|x|\le63/2048$ and $-35/2048\le y\le27/2048$. Enlarge every side by $d=1/8192$, and set

$$
\eta=35/2048+d,\qquad \sigma_-=1/2-63/2048-d,\qquad H=T/2-\eta.
$$

Throughout the enlarged rectangle $|t-T|\le\eta$ and $\sigma_-\le\sigma\le1-\sigma_-$. For any $L\ge1$, at most $2L$ Gaussian ideals have norm at most $L$. Each has one generator $u+iv$ with $u>0$ and $v\ge0$. There are at most $\lfloor\sqrt L\rfloor(1+\lfloor\sqrt L\rfloor)\le2L$ such pairs. Thus $\sum_{n\in A}|a_n|\le2L$ for every $A\subseteq\{1,\ldots,L\}$.

## The shift, including the gamma poles

Move the line of integration to $\Re z=-k$, with $k$ the positive integer in the table. The exponential decays quadratically in the vertical coordinate on every intervening vertical line. Besides $z=0$ this shift crosses the $k$ poles $z=-s-j$, $0\le j<k$, whose gamma residues have modulus $1/j!$. For these poles $|1/z|\le1/(T-\eta)$, $\sigma+j<k$, and $(n/B)^j\le(L/B)^k$ since $L>B$. The exact values of $|\Gamma(1+iv)|$ and the gamma recurrence give

$$
 S^{-1}\le \frac{e^{\pi T/2}}{D},\qquad
 D=B^2\sqrt{2\pi T(1+T^2)}.
$$

The sum of the absolute gamma-pole residues over both reflected terms is consequently bounded by

$$
 P=\frac{4Lk}{(T-\eta)D}\exp\!\left(\frac{\pi\eta}{2}+k^2
             +k\log(L/B)-(T-\eta)^2\right).
$$

On the shifted line put $u=\Im z$, $v=t+u$. For $\sigma$ in this rectangle the beta integral gives $|\Gamma(\sigma+iv)|\le\Gamma(\sigma)|\Gamma(1+iv)|$. Splitting the gamma integral at 1 bounds $\Gamma(\sigma)\le1/\sigma+e^{-1}<3$. The exact modulus of $\Gamma(1+iv)$ then yields

$$
 |\Gamma(\sigma+iv)|\le3\sqrt{1+2\pi|v|}\,e^{-\pi|v|/2}.
$$

The exponential tilt on $\Re z=-k$, the bound on $S^{-1}$, and this last factor combine to give at most $e^{\pi\eta/2}$, apart from $e^{k^2-u^2}$. Also $\sqrt{1+2\pi|v|}\le\sqrt{1+2\pi(T+\eta)}\,e^{|u|/(2T)}$.

Use the recurrence to pass from $\Gamma(\sigma+iv)$ to $\Gamma(\sigma-k+iv)$. When $|u|\le H$, the $k$ reciprocal factors together are at most $T^{-k}\exp(2k(\eta+|u|)/T)$, since $|v|\ge T-\eta-|u|$ and $-\log(1-h)\le2h$ for $0\le h\le1/2$. For $|u|>H$ the product is at most 3, since $1-\sigma>1/3$ and $j-\sigma>1$ for $j\ge2$.

Set

$$
 C=\frac{24\sqrt\pi}{2\pi k}\,
    \frac{L(B/L)^{\sigma_-}\sqrt{1+2\pi(T+\eta)}}{D}.
$$

Here $n^{k-\sigma}\le L^{k-\sigma}$, $|1/z|\le1/k$, and $\int_{\mathbb R}e^{-u^2+h|u|}\,du\le2\sqrt\pi\,e^{h^2/4}$. Counting both reflected terms and integrating the near and far parts gives respectively

$$
 U=C\exp\!\left(\frac{\pi\eta}{2}+k^2+\frac{2k\eta}{T}
      +\frac{(2k+1/2)^2}{4T^2}+k\log\frac{L}{BT}\right),
$$

$$
 V=3\sqrt2\,C\exp\!\left(\frac{\pi\eta}{2}+k^2
      +k\log(L/B)-\frac{H^2}{2}+\frac{1}{8T^2}\right).
$$

For the far integral I took out $e^{-H^2/2}$ and integrated the remaining Gaussian $e^{-u^2/2}$. The replay bounds $P$ and $V$ separately below $10^{-1000}$ in raw completion units for both cutoffs in the table. The entire difference in value has modulus bounded by $U+V+P$. Every disk of radius $d$ centered in the original rectangle lies in the enlarged one, so Cauchy’s derivative estimate bounds its derivative by $(U+V+P)/d$. These bounds concern the weight replacement on the selected norms. The smoothed contributions from intervening higher norms still depend on their signed coefficients.

## A derivative bound for the full remainder

The sharper of our absolute tail estimates uses the 404 split primes with opposite character signs and applies whenever $|x|\le1/25$ and $|y|\le1/32$. At cutoff $2^{28}$ it gives $|F-F_{2^{28}}|<7.557639\times10^{-19}$ in completed units. The same upper bound applies to $F-F_N$ for every integer $2^{28}\le N\le X=7{,}417{,}868{,}472{,}142{,}536{,}246$. To see why, use the same smoothing $G(z)=e^{z^2-i\pi z/2}$ and move all the contours for $n\le X$ to the left of zero. For $n>X$ retain the right-hand contours. After subtracting the sharp prefix, the only residues left are those at norms $N<n\le X$. The majorant sums their absolute values, and increasing $N$ removes summands. The left integral over all $n\le X$ and the right integral over all $n>X$ use the same weights at every $N$. The value of the complex remainder itself need not decrease. [Archived tail calculation](../../archive/2026-11-20-gaussian-circle-phases-v001/replay_tail.py) · [Domain and contour estimates](../../archive/2026-11-20-gaussian-reflected-disks-v001/arc-method.md)

Every point in the original rectangle is the center of a disk of radius

$$
 r=\frac{1}{25}-\frac{63}{2048}=\frac{473}{51200}
$$

inside that wider box. In particular $35/2048+r<1/32$. The replay recomputes the absolute tail estimate and applies Cauchy's derivative bound on these disks. It obtains

$$
 \frac{|(F-F_N)'(s)|}{S_0}<4.813\times10^{12}.
$$

At the original cutoff $293{,}601{,}280$, a full-factor off-line zero would require the omitted derivative to cancel the measured negative horizontal slope of the imaginary part somewhere between that zero and the critical line. The measured slope has magnitude greater than $194 S_0$ throughout the rectangle. The new absolute bound is about $2.48\times10^{10}$ times that threshold. It limits what the remaining arithmetic could do but leaves reversal possible.
