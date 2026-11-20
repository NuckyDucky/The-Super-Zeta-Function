# An upper count for the two disks from the Gaussian prime coefficients

The right disk has center `33/64+i(T_D-1/512)` and radius `15/1024`. The left disk is its reflection across the critical line. All counts below include multiplicity and the circle. The disks are disjoint. The completed Gaussian Hecke factor satisfies reflection and is entire of order one.

Write $T=T_D-1/512$, $A=\log(10^7)$, and take

$$
V(y)=(1-y)\cos(\pi y)+\sin(\pi y)/\pi \quad (0\le y\le1),
\qquad
q(v)=\frac{V(|v|/A)}{\cosh(v/2)} \quad (|v|\le A).
$$

Extend $q$ by zero and set $h(z)=\int_{-A}^A q(v)e^{ivz}\,dv$. For $|x|\le 1/2$ the real part of $h(d-ix)$ is nonnegative. Indeed on $x=\pm 1/2$ its Fourier coefficient is $q(v)\cosh(v/2)=V(|v|/A)$. This is the autocorrelation of $u\mapsto\cos(\pi u/A)\mathbf1_{|u|\le A/2}$ divided by its squared norm. The Fourier transform of that autocorrelation is a modulus squared. The maximum principle for its real harmonic extension proves nonnegativity in the strip, using uniform $O((1+|d|)^{-2})$ decay from integration by parts. Further integrations show $h(d)=O((1+|d|)^{-4})$ on the real line since $q$ is compactly supported and twice continuously differentiable with piecewise smooth third derivative.

The explicit formula evaluates $S=\sum_\rho\Re h((\gamma-T)-i(\beta-1/2))$. With $B=\sqrt Q/(2\pi)$, $Q=106039090829156$, it gives

$$
S=\frac1\pi\int_{\mathbb R} h(u)\,[\log B+\Re\psi(1/2+i(T+u))]\,du
-2\sum_{N\mathfrak p^k\le 10^7}
\frac{\eta(\mathfrak p)^k\log N\mathfrak p}{(N\mathfrak p^k)^{1/2}}
q(\log N\mathfrak p^k)\cos(T\log N\mathfrak p^k).
$$

To see the normalization, integrate the logarithmic derivative of the completion against $h(-i(w-1/2)-T)$ on opposite vertical lines at $c>1$ and $1-c$. The functional equation makes their sum twice the real part on the right. Expand the absolutely convergent Euler logarithmic derivative there. Fourier inversion gives the displayed prime factors and compact frequency support terminates the sum exactly. Shift the gamma and constant integrals to the center line, where the gamma logarithmic derivative is holomorphic through this shift. Horizontal sides may be sent to infinity through ordinates avoiding zeros by the standard explicit-formula contour argument for the Hecke completion. The constant term is $2\log B$, since $\int h/(2\pi)=q(0)=1$.

For the gamma bound the probability density $h(u)/(2\pi)$ has second moment $v=-q''(0)=\pi^2/A^2+1/4$. Euler summation gives $\Re\psi(1/2+it)\le\log(1+|t|)+\min(1,\pi/(4|t|))$, with the second argument interpreted as infinity at zero. This follows by dropping the nonpositive term $-\Re(1/(2z))$ and bounding the Bernoulli remainder by $\tfrac12\int_0^\infty[(x+1/2)^2+t^2]^{-1}dx$. Apply Jensen's inequality to the logarithm and use $\mathbb E|u|\le\sqrt v$. On $|u|\le T/2$ the remainder is at most $\pi/(2T)$. The remaining probability is at most $4v/T^2$. This proves the archimedean upper bound implemented in the replay.

The two disks both satisfy $|\gamma-T|\le15/1024$. On the support of $q$, $|v|(15/1024)<\pi/2$. Thus the cosine and $q$ are nonnegative, and $\cosh(vx)\ge1$. Each zero in these disks contributes at least $2\int_0^A q(v)\cos(15v/1024)\,dv$. The integrand decreases, giving the directed lower sum from 4,096 uniform bins. In particular the same argument actually applies throughout the full horizontal band of this half-width.

The 192-bit output gives $S<87.057901$ and each zero contributes more than $5.481507$. Each zero in the right disk comes with one in the left disk. Dividing the upper bound by twice the per-zero lower bound gives a ratio below $7.941055$. The resulting upper bound of seven per disk is compatible with zero and with one. It does not determine winding or boundary nonvanishing.

Run `python -B mass.py 10000000` to repeat this bound. The [field calculation](../2026-11-20-gaussian-endpoint-parity-v001/gaussian-hardy-endpoints.md) identifies the conductor and character. For the explicit formula in the setting of completed automorphic functions, see [Sami Omar, *On small zeros of automorphic L-functions*, §2](https://www.numdam.org/item/CRMATH_2014__352_7-8_551_0.pdf).
