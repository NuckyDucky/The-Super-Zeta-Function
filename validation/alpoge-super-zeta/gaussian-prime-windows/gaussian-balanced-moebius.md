# The two Möbius factors near the square-root norm

I can replace the signed ideal sum at scale $Y$ by a quadratic sum whose two Möbius inputs are both at scale $\sqrt Y$, up to powers of $\log Y$. I use the same Gaussian character, the same theta weight, and the same cutoff variable $Y$ as in the seventh-power-free calculation. The replacement has an error smaller than any fixed inverse power of $Y$. The estimates on the discarded terms use the actual quartic's theta reflection and ordinary Gamma identities. [Previous norm split](gaussian-moebius-content.md) · [Lean identities](GaussianBalancedMoebius.lean) · [Independent replay and axioms](gaussian-balanced-moebius-audit.txt)

## The convolution at the actual quartic

Let $B(n)=\sum_{N\mathfrak a=n}\chi(\mathfrak a)$ and $A(n)=\sum_{N\mathfrak a=n}\mu_k(\mathfrak a)\chi(\mathfrak a)$, using the archived $\chi$ over $k=\mathbb Q(i)$. Then $A*B=\mathbf 1$ under Dirichlet convolution, with $\mathbf 1$ supported at norm $1$. At each prime $p$, the local series of $A$ is the product of $1-\chi(\mathfrak p)X^{f_{\mathfrak p}}$ over the actual Gaussian primes above $p$. Lean identifies that product with the prime-power coefficients of the Dirichlet inverse of the archived $B$.

If $P(n)=A(n)$ for $n\le Z$ and $P(n)=0$ otherwise, then

$$
A=2P-P*P*B+(A-P)*(A-P)*B.
$$

The last term is supported on $n>Z^2$ because each copy of $A-P$ requires norm greater than $Z$. Lean proves the resulting exact coefficient identity for every $n\le Z^2$. This is the two-factor convolution used by Huxley and Watt for Mertens sums, applied here to the archived Gaussian coefficients. In an integer test through norm $8192$ with $Z=91$, the short sum is $-5$, the convolution sum is $-2$, and their combination $2(-5)-(-2)=-8$ matches the direct sum. Each of the $8192$ coefficients agreed separately. The test constructs $B$ by summing the three archived Legendre signs over generators $a+bi$ with $a\ge1$, $b\ge0$, and $a^2+b^2\le8192$, then computes $A$ recursively from $A*B=\mathbf 1$. [Huxley and Watt, equation (1.5)](https://arxiv.org/pdf/1807.05890#page=2) · [Actual convolution and cutoff in Lean](GaussianBalancedMoebius.lean)

## The kernel after summing the third factor

Write $C=\sqrt{26509772707289}/\pi$ and $H(v)=\Theta(v^7/C)$ as before. Write $\Lambda$ for the entire continuation of $C^z\Gamma(z)G(z)$. Summing the unrestricted $B$ variable gives the kernel

$$
K(v)=\sum_{k\ge1}B(k)H(vk),\qquad
\widehat K(z)=\tfrac17\Lambda(z/7)G(z).
$$

The transform follows by absolute convergence for $\Re z>1$. The natural Mellin convention here is $\widehat K(z)=\int_0^\infty K(v)v^{z-1}dv$. On the right line inversion follows by absolute convergence and the decay of $\widehat H$. Lean checks that $\widehat K$ continues to an entire function and, for $\Re z<0$, that reflection gives

$$
\widehat K(z)=
\frac{\Lambda(1-z/7)G(1-z)\,C^{1-2z}\Gamma(1-z)^2\sin(\pi z)}{7\pi}.
$$

This uses $\Lambda(z)=\Lambda(1-z)$ for the actual character and Euler's reflection identity for Gamma. The entire expression allows a shift from the initial line to any fixed left line. The functional equation, absolute convergence on the right, and Phragmén–Lindelöf give polynomial vertical growth on fixed strips for the Hecke factors. The initial exponential growth bound for Phragmén–Lindelöf follows from the theta integral and inverse Gamma. Stirling's formula then gives exponential vertical decay for the completed factor $\Lambda(z/7)$, so the horizontal integrals vanish. [Lean reflection](GaussianBalancedMoebius.lean) · [Euler reflection](https://dlmf.nist.gov/5.5.E3) · [Stirling in a sector](https://dlmf.nist.gov/5.11.E1)

For $\Re z=-r$ with $r=7j$ and $j\ge1$, the Hecke readings in the reflected expression are absolutely convergent and uniformly bounded. If $x>0$ and $\alpha=12\pi/25$, the complex-parameter Gamma integral gives

$$
|\Gamma(x+it)|\le \Gamma(x)(\cos\alpha)^{-x}e^{-\alpha |t|}.
$$

Use the exponential with complex rate $e^{i\alpha\,\mathrm{sgn}(t)}$ and take absolute values. The three reflected Gamma factors together give decay $e^{-(15/7)\alpha|\Im z|}$. The sine costs at most $e^{\pi|\Im z|}$, leaving $e^{-\pi|\Im z|/35}$. The factorials are $\Gamma(1+j)\Gamma(1+r)^2\le r^{15r/7}$. The remaining powers of $C$ and $\cos\alpha$ can be absorbed into $c_0^r$ with $c_0$ fixed. Inverting on this line bounds $|K(v)|$ by a constant times $(c_0 v r^{15/7})^r$. Choosing $r$ a positive multiple of $7$ of size $c_1 v^{-7/15}$ with $c_1$ sufficiently small gives $K(v)=O(e^{-c_2v^{-7/15}})$ near zero. At large $v$, the upper theta tail and $|B(k)|\le d(k)$ give $K(v)=O(e^{-c_3 v^7})$. The contour estimates and inversion in this section are written arguments. Lean checks the reflected expression and the three rational exponents used for the tails and cutoff. [Complex-parameter Gamma integral](https://dlmf.nist.gov/5.9.E1) · [Original theta tails](GaussianSeventhFreeMellin.lean)

## The remaining quadratic estimate

Let $M(Y)=\sum_n A(n)H(n/Y)$ as in the original shortened sum. For any fixed $D_0>0$ I choose a sufficiently large constant $c$ and let $L=(c\log Y)^{1/7}$, $Z=\lceil\sqrt{YL}\rceil$. The $2P$ term is negligible by the lower theta tail. The convolution error is supported at $n>Z^2$. Its coefficients are bounded by $d_6(n)$, since $|A(n)|,|B(n)|\le d(n)$, so the upper theta tail makes its total $O_{D_0}(Y^{-D_0})$. For example $d_6(n)\le n^5$ and I can take half the exponential out at $n/Y=L$ and sum the rest at cost $O(Y^6)$.

After forming $K$, if $mn/Y<L^{-15}$ or $mn/Y>L$, the corresponding tail bound for $K$ has an exponential in $L^7=c\log Y$. Such pairs contribute another $O_{D_0}(Y^{-D_0})$, since the total absolute weight of all pairs through $Z$ is polynomial in $Y$. I obtain

$$
M(Y)=-
\sum_{\substack{m,n\le Z\\YL^{-15}\le mn\le YL}}
A(m)A(n)K(mn/Y)
+O_{D_0}(Y^{-D_0}).
$$

Each variable in this sum is at least $YL^{-15}/Z\gg\sqrt Y/(\log Y)^{31/14}$ and at most $O(\sqrt Y(\log Y)^{1/14})$. The diagonal and any fixed polylogarithmic band $|m-n|\le(\log Y)^b$ already contribute $O_{\varepsilon,b}(Y^{1/2+\varepsilon})$ by boundedness of $K$ and $|A(n)|\le d(n)\ll_\eta n^\eta$. The missing estimate is cancellation in the other pairs. An $O_\varepsilon(Y^{1/2+\varepsilon})$ bound there gives the original square-root estimate. With ordinary RH and the Gaussian zero-free input from the earlier split, the same quadratic sum represents the large-primitive-norm part up to $O(Y^{1997/4000})$. [Original square-root criterion](gaussian-seventh-free.md#why-seven-works) · [Bound below the primitive cutoff](gaussian-moebius-content.md)

If I take two scale differences, I can also bound the signed block with $\max(m,n)/\gcd(m,n)\le Y^{3/14}$ at the square-root scale. The differences leave the Mellin reading nonzero as a multiplier throughout $\Re z>1/2$. [Common-divisor and scale calculation](gaussian-moebius-common-divisor.md)
