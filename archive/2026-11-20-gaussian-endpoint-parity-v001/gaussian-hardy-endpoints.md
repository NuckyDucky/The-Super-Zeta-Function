# The Gaussian endpoint signs at the Dottie height

I tested the endpoints $t_\pm=T_D\pm1/16$ for the quadratic Hecke character $\eta_\delta$ of $k=\mathbb Q(i)$ belonging to $K=k(\sqrt\delta)$, where $\delta=-5045155+1027708i$. Its completed function, up to a positive constant, is $C(s)=B^s\Gamma(s)L(s,\eta_\delta)$ with $B=\sqrt{Q}/(2\pi)$ and $Q=106039090829156$. It is entire, real on the real axis, and has root number $+1$, since it is the quotient of the completed Dedekind functions of $K$ and $k$. Write $s=1/2+it$. My signed observable is the real value $H(t)=C(s)/|B^s\Gamma(s)|$. [Field and character calculation](https://github.com/NuckyDucky/The-Super-Zeta-Function/tree/e34952209e784b7a791a7c4735e91258d58d558d/archive/2026-11-20-dedekind-phase-v001)

## A finite measurement and its uncomputed tail

The Dirichlet coefficient $a_n$ sums the exact ray-character signs of all ideals of norm $n$. The Gaussian integers are principal, and the generators $a+bi$ with $a>0,\ b\ge0$ count each ideal once. Thus $|a_n|\le d(n)$, the ordinary divisor count. I formed

$$
P_N(t)=2\sum_{n\le N}\frac{a_n}{\sqrt n}
\cos\big(t\log B+\Im\log\Gamma(1/2+it)-t\log n\big).
$$

At $N=65536$ there are 8022 nonzero coefficients. The values are $-3.75294732385921\ldots$ and $2.26206491139767\ldots$. The difference between this polynomial and the first $N$ terms of the exact smoothed formula below is smaller than $4.213\times10^{-12}$. The bound for the omitted norms is much larger: the final signed interval at each point contains zero, with radius less than $5.999\times10^{12}$. At $N=262144$ the two finite values are both positive. Increasing the cutoff to $1048576$ changes the apparent sign pattern again. No Gaussian sign bracket can be credited from these readings. [Directed endpoint values and finite-prefix sweep](gaussian-hardy-endpoints-balls.json) · [Replay in Python with python-flint 0.9.0](check_gaussian_hardy_endpoints.py)

## Proof of the enclosures

Use $G(z)=\exp(z^2-i\pi z/2)$ and weights
$$
W_s(n)=\frac1{2\pi i}\int_{\Re z=1}
\frac{G(z)}{z}\frac{\Gamma(s+z)}{\Gamma(s)}(B/n)^z\,dz .
$$
Shift the contour for $C(s+z)G(z)/z$ from $1$ to $-1$. Its only pole is at $z=0$. Applying $C(s-z)=C(\bar s+z)$, $G(-\bar z)=\overline{G(z)}$, and expanding the Dirichlet series on the right-hand line gives the exact formula
$$
 H(t)=2\Re\left(e^{i\arg(B^s\Gamma(s))}
      \sum_{n\ge1}a_n n^{-s} W_s(n)\right).
$$
Gaussian decay in $\Im z$ justifies the shift and absolute convergence there. [Rubinstein, smoothed approximate functional equation](https://arxiv.org/abs/math/0412181)

On $z=1+iu$, use the gamma recurrence and $|\Gamma(1/2+iv)|^2=\pi/\cosh(\pi v)$. The factor $\exp(\pi u/2)\sqrt{\cosh(\pi t)/\cosh(\pi(t+u))}$ is at most $\sqrt2$ for $t>0$. Thus
$$
 |W_s(n)| \le \frac{e\sqrt2}{2\pi}\frac Bn\int_{\mathbb R}
 e^{-u^2}(t+|u|+1/2)\,du
 \le 2B(t+2)/n .
$$
Shifting the **weight** integral to $\Re z=-1$ crosses $z=0,-s$. The residue at zero is 1. The residue at $-s$ has magnitude at most $e^{1/4-t^2}\sqrt{n/B}/(t\sqrt\pi)\le n/(Bt)$ for $n\ge1,\ B<2\,000\,000,\ t>10$. On the new vertical line the recurrence puts $\sqrt{1/4+(t+u)^2}$ in the denominator. For $|u|\le t/2$ its reciprocal is at most $2/t$, and elsewhere it is at most 2. The bound $\int_{|u|>t/2}e^{-u^2}du\le2e^{-t^2/4}/t$ gives
$$
 \left|\frac1{2\pi i}\int_{(-1)}\cdots\,dz\right|
 \le \frac{e\sqrt2}{2\pi}\frac n{Bt}(2\sqrt\pi+4e^{-t^2/4})
 \le 3n/(Bt).
$$
It follows that $|W_s(n)-1|\le4n/(Bt)$ and that replacing each weight by 1 in the first $N$ terms costs at most $8\sum_{n\le N}|a_n|\sqrt n/(Bt)$.

Split the remaining terms at $M=8\times10^{18}$, verifying $B(t+2)<M<2Bt$ by ball arithmetic. Up to $M$ we have $|W_s(n)|\le9$. Since $\sum_{n\le M}d(n)/\sqrt n\le2\sqrt M(1+\log M)$, the entire contribution from $N<n\le M$ has magnitude at most $36\sqrt M(1+\log M)$. For the rest, partial summation from $\sum_{n\le u}d(n)\le u(1+\log u)$ gives $\sum_{n>M}d(n)n^{-3/2}\le3(\log M+3)/\sqrt M$. The outer contribution is at most $12B(t+2)(\log M+3)/\sqrt M$. These are absolute bounds that make no assumption on cancellation, ERH, or the signs at either endpoint. The transition scale $Bt$ at the center is $7.417868472142536246\ldots\times10^{18}$. This scale describes this direct evaluation method.
