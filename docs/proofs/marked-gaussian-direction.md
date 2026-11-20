# Recovering a quartic splitting sign from a marked Gaussian direction

My reciprocal fixed pair supplies two ordered exponents, $U=LQ$ and $V=-LP$. On the branch $U=u\tan u+iu$, $V=u\tan u-iu$, their ratio at $u=\pi/4$ is $i$. I mark an integer combination of the two exponents and divide by $V$. Its value is $z=(aV+bU)/V=a+bi$. The angle I measure below is the direction of this **marked lattice point**. The fixed pair supplies the two basis vectors. The integers $a,b$ specify which point I am reading. [My original fixed-pair parametrization](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L145-L190) · [Ordered lifts, equation (1)](../../archive/2026-11-18-lean-foundations-v001/notes/monodromy.md#1-coordinates-and-constants) · [The two lifts and their arithmetic weights](../../archive/2026-11-20-dedekind-phase-v001/README.md)

The arithmetic question comes from the same six integers that gave my approximation to $\pi$. Write $N=465x^2-183x-659$ and $D=155x^2+396x-936$. My quartic factors over the Gaussian integers as $f(x)=G(x)\overline{G}(x)$ with $G=(N-D)+2iN$. The discriminant of this quadratic is $\delta=-5045155+1027708i$. For every Gaussian prime ideal $\mathfrak p$ coprime to $2\delta$, define $\psi(\mathfrak p)$ to be $+1$ if $\delta$ is a square in its residue field and $-1$ otherwise. This is the splitting sign for the extension $\mathbb Q(i,\sqrt{\delta})/\mathbb Q(i)$. Extend $\psi$ multiplicatively to integral ideals coprime to $2\delta$. [The original quartic](../../archive/2026-11-18-lean-foundations-v001/arithmetic/research/geometry.md) · [Relative field and Euler factors](../../archive/2026-11-20-dedekind-phase-v001/README.md)

## Proposition

Let $p\equiv1\pmod4$ be a rational prime and let $\mathfrak p$ be one of its two Gaussian prime factors, coprime to $2\delta$.

1. The direction of its generator modulo $\pi/2$ recovers $\mathfrak p$ and its splitting sign. Among such prime ideals of norm at most $X$, an angular error strictly less than $\tfrac12\arcsin(1/X)$ still determines the marked ideal uniquely.
2. On all integral ideals coprime to $2\delta$, the direction loses information. Multiplying any such ideal by $(73)$ preserves its direction and reverses its splitting sign.

### Recovering a prime and its sign

The four Gaussian units rotate a generator through multiples of $\pi/2$. Choose the unique representative $a+bi$ with $a,b>0$. Its norm $a^2+b^2=p$ is prime, so $a,b$ are coprime. The exact direction $\theta\in(0,\pi/2)$ gives $\tan\theta=b/a$ in lowest terms. Its numerator and denominator recover both coordinates, hence $p$ itself. In the residue field $\mathbb F_p$, the generator vanishes and $i\equiv-ab^{-1}\pmod p$. For $\delta=d_0+d_1i$ this gives the ordinary Legendre symbol

$$
\psi(\mathfrak p)=\left(\frac{d_0-d_1ab^{-1}}{p}\right).
$$

For the precision bound, take two distinct candidate ideals and choose generators $z=a+bi$ and $z'=c+di$, rotating by units to realize the smallest angular separation $\eta$ modulo $\pi/2$. Then $0\leq\eta\leq\pi/4$. The determinant $ad-bc$ is a nonzero integer, since equality of direction would recover the same primitive generator. Consequently

$$
\sin\eta=\frac{|ad-bc|}{|z|\,|z'|}\geq\frac{1}{X}.
$$

Intervals of radius strictly less than half this minimum angular separation can contain at most one candidate. For norms up to $1{,}000$, an absolute error of $0.0005$ radians suffices. The bound gives uniqueness when the measured angle comes from a prime within the stated norm range.

### The two directions above 73

The factorization $73=(8+3i)(8-3i)$ gives the first-quadrant generators $8+3i$ and $3+8i$ for the two ideals. Their angles are approximately $0.358771$ and $1.212026$ radians. Substituting their residues for $i$ gives these exact computations.

| Generator | Residue of $i$ modulo $73$ | Residue of $\delta$ | Residue of $\delta^{36}$ | $\psi$ |
| --- | ---: | ---: | ---: | ---: |
| $8+3i$ | $46$ | $8$ | $1$ | $+1$ |
| $3+8i$ | $27$ | $34$ | $72$ | $-1$ |

The equal norms hide the distinction between the conjugate primes. Their two directions recover it. For the product ideal, multiplicativity now gives $\psi((73))=-1$. Positive real scaling preserves the direction of every nonzero $z$, so $(z)$ and $(73z)$ have the same direction while their signs are opposite whenever $(z)$ is coprime to $2\delta$. Already $z=1$ gives both signs on the positive real axis.

This establishes exactly which marked input the recovery uses. On the split primes, the direction recovers the primitive Gaussian generator, and the discriminant from my quadratic supplies the sign test. On general ideals, the same ray can contain both signs. The question of whether a spectral reading supplies the marked direction with the required precision is a separate measurement to make on the original dynamics.
