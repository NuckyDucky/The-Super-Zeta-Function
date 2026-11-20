# The two Gaussian critical-line values at the edges of the Dottie interval

For the quadratic Hecke character $\eta_\delta$ over $\mathbb Q(i)$, let $B=\sqrt{106039090829156}/(2\pi)$ and $S=B^2|\Gamma(2+iT_D)|$. At the two endpoints $t_\pm=T_D\pm1/16$, the functional equation makes $f(1/2+it)=B^{1/2+it}\Gamma(1/2+it)L(1/2+it,\eta_\delta)/S$ real. The separate bounds are

$$
|f(1/2+it_-)|<3.584\times10^{-19},\qquad
|f(1/2+it_+)|<2.945\times10^{-19}.
$$

I counted the cancellation between prime ideals at the same norm, including the two ideals above $73$. This reduces the radius of the earlier absolute error bound on the Gaussian Hardy function from $5.999\times10^{12}$ to less than $6.564\times10^9$. Both enclosures still contain positive and negative values. Doubling the norm cutoff from $2^{20}$ to $2^{21}$ changes the lower endpoint's finite sum from $-0.547356$ to $+0.935248$. The upper endpoint's finite sum changes from $+0.017837$ to $+0.198664$. Neither sign of the full function is determined. [Directed calculations](endpoint-refinement.json) · [Reproduction script](check_endpoint_refinement.py)

## Counting absolute coefficients at split primes

Write $a_n=\sum_{N\mathfrak a=n}\eta_\delta(\mathfrak a)$. If the symbols at the two primes over a split rational prime $p$ are opposite, their local product is $(1-X^2)^{-1}$, where $X=p^{-s}$. Thus $a_{p^j}=0$ at odd powers and $a_{p^j}=1$ at even powers. The local product counting all Gaussian ideals at this prime is $(1-X)^{-2}$. For any finite set $P$ of such primes, the coefficients of

$$
\zeta_{\mathbb Q(i)}(s)\prod_{p\in P}\frac{1-p^{-s}}{1+p^{-s}}
$$

majorize $|a_n|$ termwise. At primes in $P$ the coefficients agree. At all other primes the number of ideals bounds their signed sum, also at powers, and multiplication establishes the claim for all norms.

Put $A=(\pi/4)\prod_{p\in P}(p-1)/(p+1)$ and $E=\prod_{p\in P}(\sqrt p+1)/(\sqrt p-1)$. Then

$$
\sum_{n\le x}|a_n|\le Ax+E\sqrt x\qquad(x\ge0).
$$

Indeed the untwisted Gaussian ideal count differs from $\pi x/4$ by at most $\sqrt x$. Sum $\lfloor\sqrt{x-j^2}\rfloor+1$ for integers $1\le j\le\sqrt x$. The decreasing quarter-circle heights bound the error from replacing this sum by its integral: the right-endpoint sum of the heights is at most the integral and at least the integral minus $\sqrt x$. The floor-plus-one correction adds between zero and $\sqrt x$. For $x<1$ the same bound holds directly. Convolve the count with the coefficients $b_d$ of the displayed finite product. The signed sum $\sum_d b_d/d$ gives the factor multiplying $\pi x/4$, and $\sum_d |b_d|/\sqrt d=E$ bounds the errors, since $(1-X)/(1+X)=1+2\sum_{j\ge1}(-X)^j$. The bound at $x/d<1$ permits summation over all $d$. In this calculation $404$ split primes through $13697$ give $A<0.463399$ and $E<1729272$.

## A real weight for the smoothed functional equation

Let $s=1/2+it$, $U=Bt$, and $\theta=t\log B+\Im\log\Gamma(s)$. Write $H(t)=e^{i\theta}L(s,\eta_\delta)$, so $f(s)=H(t)|B^s\Gamma(s)|/S$. With the integration line oriented upward, the root-number $+1$ functional equation and a contour shift give

$$
H(t)=2\Re\left[e^{i\theta}\sum_{n\ge1}a_n n^{-s} W_s(n)\right],\qquad
W_s(n)=\frac1{2\pi i}\int_{(1)}
e^{z^2-i\pi z/2}\frac{\Gamma(s+z)}{\Gamma(s)}
\left(\frac Bn\right)^z\frac{dz}{z}.
$$

In the integral for the completed function, shifting from $1$ to $-1$ crosses the residue at zero. The functional equation, real coefficients and $G(-\bar z)=\overline{G(z)}$ for $G(z)=e^{z^2-i\pi z/2}$ identify the two integrals as conjugates. [Rubinstein, smoothed approximate functional equations](https://arxiv.org/abs/math/0412181)

Replacing the gamma ratio by $(it)^z$ with the principal logarithm gives $V_U(n)=\tfrac12\mathrm{erfc}(\log(n/U)/2)$. Equivalently $V_U(n)=\Pr(Ue^Z\ge n)$ with $Z$ real normal of mean $0$ and variance $2$. The identity follows by differentiating the inverse Mellin integral in $\log U$, taking the Fourier transform of a Gaussian and using its limit at $U=0$.

At both specified heights I obtain $|W_s(n)-V_U(n)|\le3B/n$ simultaneously for all $n$. To check the constant, set $z=1+iu$ and $R(z)=\Gamma(s+z)/[\Gamma(s)(it)^z]$. The remaining integral is bounded by $U/n$ times $\int_{\mathbb R} e^{1-u^2}|R(z)-1|\,du/(2\pi|z|)$. For $|u|\le12$ write $\log R=z\int_0^1[\psi(s+\tau z)-\log(it)]\,d\tau$, choosing the continuous logarithm. For $\Re w>0$, $\Im w=v>0$, first-order Euler summation gives $|\psi(w)-\log w|\le(1/2+\pi/4)/v$: the endpoint term is at most $1/(2v)$ and the periodic Bernoulli remainder is bounded by $\tfrac12\int_0^\infty[(x+\Re w)^2+v^2]^{-1}dx\le\pi/(4v)$. Integration of $1/w$ on the segment from $it$ bounds the remaining logarithm. Together these give

$$
|\log R|\le\frac{|z|(1+\pi/4+|z|)}{t-14}\le\frac{210}{t-14}.
$$

Use $|e^h-1|\le|h|e^{|h|}$ and $|z|\le 1+|u|$. The portion $|u|\le12$ of the integral after extracting $U/n$ is at most

$$
\frac{e}{2\pi}\big((2+\pi/4)\sqrt\pi+1\big)
\frac{\exp(210/(t-14))}{t-14}.
$$

On the complement the gamma recurrence and $|\Gamma(1/2+iv)|^2=\pi/\cosh(\pi v)$ give $|R|\le\sqrt2(t+|u|+1/2)/t$. Using $|z|\ge1$ and the Gaussian tail on $|u|>12$ adds at most

$$
\frac{e^{-143}}{2\pi}
\left[\frac{1+\sqrt2(1+1/(2t))}{12}+\frac{\sqrt2}{t}\right].
$$

The script checks that the sum of the last two bounds, multiplied by $t$, is below $3$. In the entire Hardy sum, $W_s\mapsto V_U$ costs at most $6B\zeta_{\mathbb Q(i)}(3/2)\le6B\zeta(3/2)$, since the alternating Dirichlet beta series is at most $1$ at $3/2$.

## The reported remainder

At $N=2^{21}$ the finite polynomial sums $2a_n\cos(\theta-t\log n)/\sqrt n$ exactly up to the indicated interval arithmetic. Replacing $V_U(n)$ by $1$ for these terms costs at most their absolute-amplitude sum times $e^{-h^2}/(2\sqrt\pi h)$, where $h=\log(U/N)/2>0$. For $x\ge N$, partial summation using the absolute counting estimate gives

$$
\sum_{N<n\le x}\frac{|a_n|}{\sqrt n}
\le 2A\sqrt x+E(1+\tfrac12\log(x/N)).
$$

For every $x>0$ this holds with $\log_+(x/N)$ on the right. Take expectations at $x=Ue^Z$. Here $\mathbb E\sqrt x=\sqrt Ue^{1/4}$ and $\mathbb E\log_+(x/N)\le\log(U/N)+2/\sqrt\pi$. The doubled smoothed tail is therefore at most

$$
4A\sqrt U e^{1/4}
+2E\left[1+\tfrac12\left(\log(U/N)+2/\sqrt\pi\right)\right].
$$

On the next block $2^{21}<n\le2^{22}$ I also evaluated the absolute cosine contributions with their actual angles. Their sum in the real $V_U$ series exceeds $432.65$ at the lower endpoint and $432.35$ at the upper endpoint. The script uses the minimum of $V_U$ over the block and both endpoints as a common lower bound. Thus even exact knowledge of every individual amplitude in this block, followed by a triangle inequality about the published prefix, gives a radius hundreds of times larger than that prefix. These measured numbers are lower bounds on the sum of absolute values; the **signed** block can be much smaller. The next improvement must retain cancellation among norms or evaluate more of the signed series. Multiplication by the positive factor $|B^s\Gamma(s)|/S$ gives the reported normalized intervals.
