# The quartet spectrum is an explicit Fredholm spectrum

This reader’s edition follows my proof of 16 November 2026 and keeps its equation numbering. The original is archived under my GitHub name, NuckyDucky.
[Original archived proof at commit fc74801](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/fc74801e6ea3df94406bfc9576016ece3e5e2364/archive/2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md)

I start with a fixed pair of the reciprocal tower whose two-step return has derivative one. Its ordered exponents are $\alpha$ and $\alpha^{-1}$. I take their difference and divide by $2i$.

$$
\boxed{u=\frac{\alpha-\alpha^{-1}}{2i}.}
$$

Each zero of $\cos^2u-u^2$ recovers one ordered pair of exponents and its logarithmic parameter.
At unit coupling the boundary operator has exactly the roots of $u=\cos u$ as its eigenvalues. The negatives of those roots solve $u=-\cos u$. Squaring therefore gives one entry per sign pair in the full cosine root set.

I obtain the determinant by forming the trace-class square of the operator’s inverse. Its determinant gives the product over the squared roots. Summing principal inverse powers of those roots defines the spectral zeta.
Varying the endpoint weight gives the coupling variable. The zeta splits into a double half-integer reference sum and a Mellin integral that accounts for the change in the determinant.

- [Ordered phases and parameters](#1-exact-recovery-of-every-ordered-phase-and-parameter)
- [Boundary operator and inverse](#2-a-boundary-operator-with-compact-inverse-and-the-cosine-spectrum)
- [Fredholm determinant and finite matrices](#3-exact-fredholm-determinant-and-controlled-finite-matrices)
- [Canonical product and exact traces](#4-canonical-product-and-exact-rational-trace-sums)
- [Two-variable spectral zeta](#5-a-two-variable-zeta-for-the-inverse-cosine-coupling-family)
- [Cosine inversion and its critical values](#6-exact-relation-to-the-2024-inverse-function-frontier)
- [Reproducible checks](#reproducible-checks)

## 1. Exact recovery of every ordered phase and parameter

At a fixed pair the derivative of the two-step return is the product of the two ordered exponents $U,V$. When that product is one they are reciprocal. The fixed-pair equation then gives the following relation and recovers the logarithmic lift $L$.

<a name="eq-1"></a>

$$
\alpha^2e^{\alpha-1/\alpha}=-1,\qquad
U=\alpha,\quad V=\alpha^{-1},\quad
L=-e^{-\alpha}/\alpha.
\qquad\text{(1)}
$$

Put $u=(\alpha-\alpha^{-1})/(2i)$. Equation [(1)](#eq-1) says
$\alpha e^{iu}=\sigma i$ for a unique $\sigma\in\{1,-1\}$.
Substitution into the defining equation for $u$ gives

<a name="eq-2"></a>

$$
\boxed{u=\sigma\cos u.}
\qquad\text{(2)}
$$

Conversely, every zero of $D(u)=\cos^2u-u^2$ has $u\ne0$ and a unique
$\sigma=\cos u/u\in\{1,-1\}$. The sign and the root give both ordered exponents and $L$.

<a name="eq-3"></a>

$$
\boxed{\alpha=\sigma i e^{-iu}=\sigma\sin u+iu,\qquad
\alpha^{-1}=\sigma\sin u-iu,\qquad
L=\sigma i e^{-\sigma\sin u}.}
\qquad\text{(3)}
$$

Indeed the two phase expressions have product $\sin^2u+u^2=1$, by [(2)](#eq-2),
and $\alpha^2e^{2iu}=-1$. The formula for $L$ in [(3)](#eq-3) follows from [(1)](#eq-1).
Thus each zero of $D$ gives exactly one ordered fixed pair at multiplier one, and every such pair occurs.
On the punctured $\alpha$-plane the formula for $u$ gives a quadratic in $\alpha$.
It has two preimages counted with multiplicity, coalescing when $u=\pm1$.
Equation [(3)](#eq-3) selects its unique preimage on the compatibility locus.

For the positive Dottie root $d=\cos d$, equation [(3)](#eq-3) is
$\alpha=\sin d+id$, $L=ie^{-\sin d}$. The nonunit phases below use the same recovery formula at complex roots.

Exchanging the two exponents and conjugating them act on $u$ as follows.

$$
\alpha\mapsto\alpha^{-1}\quad\longleftrightarrow\quad u\mapsto-u,
$$

<a name="eq-4"></a>

$$
\alpha\mapsto\bar\alpha\quad\longleftrightarrow\quad u\mapsto-\bar u.
\qquad\text{(4)}
$$

Exchanging the exponents sends $L$ to $-L$. Conjugating the exponents sends $L$ to $\bar L$. Together the two operations give the four transformations of a nonreal quartet.

For each positive level $n$, choose the nonunit phase $e^{t_n+i\theta_n}$ with positive log-modulus $t_n$ and argument $\pi/2<\theta_n<\pi$. Its representative $u_n$ has imaginary part $t_n$.

<a name="eq-5"></a>

$$
u_n=x_n+it_n,\qquad
x_n=\cosh t_n\sin\theta_n=(n+\tfrac12)\pi-\theta_n.
\qquad\text{(5)}
$$

In particular $(n-1/2)\pi<x_n<n\pi$, and
$u_n=\pi n+i\log(2\pi n)+O(\log n/n)$. The complete D-zero set is
$\pm d$ and $\pm u_n,\pm\bar u_n$, $n\ge1$. A multiple zero would give $\sigma\sin u=-1$, hence $u^2=0$, contradicting [(2)](#eq-2).

Lean’s **determinant_root_iff** identifies the scalar determinant zeros with images of characteristic phases. **recover_fixed_pair** recovers the ordered fixed pair and its multiplier one from a characteristic phase. **coupledDet_simple** proves simplicity for the scalar determinant in the squared spectral variable.
[Phase correspondence and recovery](../../lean/SuperZeta/Quartet.lean#L81-L111) · [Squared determinant and its simple zeros](../../lean/SuperZeta/CoupledDeterminant.lean#L65-L86)

## 2. A boundary operator with compact inverse and the cosine spectrum

I adjoin a scalar $c$ to a square-integrable function $f$ on $(-1,1)$, giving the space $\mathcal H=L^2(-1,1)\oplus\mathbb C$. In the operator domain, $f$ has a square-integrable weak derivative and $c$ is its value at zero. The operator takes $-i$ times the derivative in the function coordinate and the weighted average of the two endpoint values in the scalar coordinate. The coupling $\varepsilon$ is that weight and is nonzero.

<a name="eq-6"></a>

$$
\mathcal A_\varepsilon(f,c)=
\left(-if',\ \frac\varepsilon2[f(1)+f(-1)]\right),
\quad
\mathcal D(\mathcal A_\varepsilon)
=\{(f,c):f\in H^1(-1,1),\ c=f(0)\}.
\qquad\text{(6)}
$$

The domain is dense because an arbitrarily narrow smooth bump about zero can prescribe the value there with arbitrarily small change in $L^2$ norm. The operator is closed because convergence in its graph norm controls the $H^1$ norm of $f$ and hence the values at the midpoint and endpoints.

For an eigenvalue $u$, the first coordinate solves a constant-coefficient differential equation with $f(0)=c$, giving $f(x)=c e^{iux}$. Averaging its two endpoint values in the scalar equation gives

<a name="eq-7"></a>

$$
\boxed{u=\varepsilon\cos u.}
\qquad\text{(7)}
$$

There is a mixed-type functional differential equation precedent for this characteristic equation. In Hupkes’s formula, put the two delays at $-1$ and $1$, give each coefficient $i\varepsilon/2$, and set $z=iu$. Then $\Delta(iu)=i(u-\varepsilon\cos u)$. Hupkes uses a continuous-history space. The space in [(6)](#eq-6) lets me compute a Hilbert–Schmidt inverse and its Fredholm determinants.
[Hupkes (2008), §2.3, eq. (2.19), and §2.4](https://math.leidenuniv.nl/scripties/PhdHupkes.pdf#page=59)

If $c$ vanished, the eigenfunction would vanish. Solving at $u=0$ gives the bounded
inverse explicitly.

<a name="eq-8"></a>

$$
\boxed{\mathcal B_\varepsilon(h,k)=
\left(\frac i2\int_{-1}^1\operatorname{sgn}(x-t)h(t)dt+
\frac{k}{\varepsilon},\quad
\frac{k}{\varepsilon}-\frac i2\int_{-1}^1\operatorname{sgn}(t)h(t)dt\right).}
\qquad\text{(8)}
$$

It maps into the domain in [(6)](#eq-6), and direct differentiation/boundary evaluation
checks both inverse identities. The integral block is Hilbert–Schmidt and
the remaining blocks have finite rank. In fact

<a name="eq-9"></a>

$$
\boxed{\|\mathcal B_\varepsilon\|_2^2
=\frac32+\frac3{|\varepsilon|^2}.}
\qquad\text{(9)}
$$

The square $\mathcal B_\varepsilon^2$ is trace class because $\mathcal B_\varepsilon$ is Hilbert–Schmidt. Each nonzero eigenvalue of the compact inverse is the reciprocal of an eigenvalue found from [(7)](#eq-7). Generalized multiplicities agree with those of
$\cos u-u/\varepsilon$, as follows either from the explicit resolvent
or the determinant identity proved next.

## 3. Exact Fredholm determinant and controlled finite matrices

**Theorem.** For $\varepsilon\ne0$, the second regularized determinant is

<a name="eq-10"></a>

$$
\boxed{\det{}_2(I-u\mathcal B_\varepsilon)
=e^{u/\varepsilon}(\cos u-u/\varepsilon),}
\qquad\text{(10)}
$$

and the ordinary trace-class determinant is

<a name="eq-11"></a>

$$
\boxed{\det(I-\lambda\mathcal B_\varepsilon^2)
=E_\varepsilon(\lambda)
:=\cos^2\sqrt\lambda-\lambda/\varepsilon^2.}
\qquad\text{(11)}
$$

The expression on the right is entire in $\lambda$ because its power series removes
the square root. At $\varepsilon=1$ its zeros encode every original parabolic
phase and parameter through [(3)](#eq-3) and sign pairing.

**Proof by explicit projection.** Partition $(-1,1)$ into an even number $N$ of
equal cells. Project the $L^2$ component onto its cellwise constants and retain
the scalar component. In the orthonormal basis, the finite matrix has blocks

$$
(B_N)_{jk}=\frac iN\operatorname{sgn}(j-k),\quad
(B_N)_{j,N+1}=\frac{\sqrt{2/N}}\varepsilon,
$$

$$
(B_N)_{N+1,j}=-\frac i2\sqrt{2/N}\,s_j,\quad
(B_N)_{N+1,N+1}=1/\varepsilon,
$$

where $s_j$ is $-1$ on the first half and $+1$ on the second half.
Only the integral kernel's diagonal cells contribute to projection error.

<a name="eq-12"></a>

$$
\|\mathcal B_\varepsilon-B_N\|_2^2=1/N.
\qquad\text{(12)}
$$

Finite elimination gives

<a name="eq-13"></a>

$$
\delta_{N,\varepsilon}(u):=\det(I-uB_N)
=\frac{(1+iu/N)^N+(1-iu/N)^N}{2}
-\frac u\varepsilon(1+u^2/N^2)^{N/2}.
\qquad\text{(13)}
$$

One may derive [(13)](#eq-13) by subtracting consecutive integral rows: their successive
homogeneous values have ratio $(1+iu/N)/(1-iu/N)$. The two half-interval
transfers have $N/2$ steps. Substitution into the retained midpoint boundary row
gives the numerator in [(13)](#eq-13). The cell factors clear the transfer denominators.
Equivalently, the integral block determinant is the first term in [(13)](#eq-13), and
its rank-one boundary Schur complement contributes the second term. These
identities are polynomial, so the intermediate exceptional denominator values
are covered by polynomial continuation.

Since $\operatorname{tr}(B_N)=1/\varepsilon$, its regularized determinant is
$e^{u/\varepsilon}\delta_{N,\varepsilon}(u)$. Formula [(13)](#eq-13) converges locally uniformly
to $\cos u-u/\varepsilon$. Hilbert–Schmidt continuity of $`\det{}_2`$ and [(12)](#eq-12) give [(10)](#eq-10).
Multiplying [(10)](#eq-10) at $u$ and $-u$ cancels the exponentials and gives [(11)](#eq-11).
For each eigenvalue $\nu$ of $\mathcal B_\varepsilon$, the pair of regularized factors becomes
$1-u^2\nu^2$. This also follows by trace-class convergence of $B_N^2$ to $\mathcal B_\varepsilon^2$. ∎

I use the determinant conventions and projection framework in Bornemann to derive
the boundary operator’s determinant, finite formula, and error constants for the cosine/quartet family.
[Bornemann (2010), §§2–5](https://arxiv.org/pdf/0804.2543).

### A useful all-N numerical bound

For $|u|\le r<N$, put

$$
\eta_N=\frac{r^3}{3N^2(1-r/N)},\qquad
\widetilde\eta_N=\frac{r^4}{4N^3(1-r^2/N^2)},
$$

$$
e_N=e^r(e^{\eta_N}-1)+\frac r{|\varepsilon|}
(e^{\widetilde\eta_N}-1),\qquad
M=e^r+r/|\varepsilon|.
$$

The logarithmic Taylor remainders of the two factors in [(13)](#eq-13) give

<a name="eq-14"></a>

$$
\boxed{|e^{-u^2/(2N)}\delta_{N,\varepsilon}(u)
-(\cos u-u/\varepsilon)|\le e_N,}
\qquad\text{(14)}
$$

<a name="eq-15"></a>

$$
\boxed{|e^{-\lambda/N}\det(I-\lambda B_N^2)-E_\varepsilon(\lambda)|
\le e_N(2M+e_N),\quad |\lambda|\le r^2.}
\qquad\text{(15)}
$$

This is a controlled $O(N^{-2})$ approximation after the explicit trace
counterterm. The uncorrected matrices have
$\operatorname{tr}(B_N^2)=1+\varepsilon^{-2}-1/N$, explaining that counterterm directly.

The boundary-operator identities [(10)](#eq-10) and [(11)](#eq-11) are proved by the projection argument above for $\varepsilon\ne0$. The Lean theorem below concerns the scalar determinant and its zero product at unit coupling.

## 4. Canonical product and exact rational trace sums

At $\varepsilon=1$, $E$ has order $1/2$ and $E(0)=1$. The trace-class determinant gives
the absolutely locally convergent product

<a name="eq-16"></a>

$$
\boxed{E(\lambda)=
\left(1-\frac\lambda{d^2}\right)
\prod_{n\ge1}
\left(1-\frac\lambda{u_n^2}\right)
\left(1-\frac\lambda{\bar u_n^2}\right).}
\qquad\text{(16)}
$$

Its logarithmic coefficients are exact power traces:

$$
\mathcal Z(m;1)=\operatorname{tr}(\mathcal B_1^{2m})
=d^{-2m}+2\Re\sum_{n\ge1}u_n^{-2m}.
$$

Since

$$
E_\varepsilon(\lambda)
=1-(1+\varepsilon^{-2})\lambda+
\sum_{m\ge2}\frac{(-1)^m2^{2m-1}}{(2m)!}\lambda^m,
$$

Newton identities show every positive-integer trace is in
$\mathbb Q[\varepsilon^{-2}]$. At $\varepsilon=1$ these give the following values.

<a name="eq-17"></a>

$$
\boxed{\mathcal Z(1)=2,\quad\mathcal Z(2)=10/3,\quad
\mathcal Z(3)=92/15,\quad\mathcal Z(4)=3538/315.}
\qquad\text{(17)}
$$

The first identity explicitly couples Dottie to every nonunit quartet:

<a name="eq-18"></a>

$$
\boxed{d^{-2}+2\Re\sum_{n\ge1}(x_n+it_n)^{-2}=2.}
\qquad\text{(18)}
$$

For $m\ge1$ and $N\ge1$, equation [(5)](#eq-5) gives the following tail bound.

<a name="eq-19"></a>

$$
\left|2\Re\sum_{n>N}u_n^{-2m}\right|
\le\frac{2\pi^{-2m}}{2m-1}(N-1/2)^{1-2m}.
\qquad\text{(19)}
$$

At $\varepsilon=1$, Lean’s **UnitSpectrum.determinant_product** proves the scalar identity [(16)](#eq-16) for every complex argument, using the classified squared roots. **first_four_unit_coupling_traces** checks the first four coefficients in [(17)](#eq-17) through the scalar determinant’s Newton identities.
[Canonical product theorem](../../lean/SuperZeta/UnitSpectrum.lean#L26-L32) · [Determinant coefficients and trace identities](../../lean/SuperZeta/Spectrum.lean#L65-L88)

## 5. A two-variable zeta for the inverse-cosine coupling family

For $\varepsilon>0$, enumerate the zeros $\lambda_j$ of $E_\varepsilon$ with algebraic
multiplicity, and use their principal logarithms. Since $E_\varepsilon(-t)>0$ for $t\ge0$,
the negative real axis is an admissible spectral cut. Define

<a name="eq-20"></a>

$$
\boxed{\mathcal Z(s;\varepsilon)=\sum_j\lambda_j^{-s},
\qquad\Re s>1/2.}
\qquad\text{(20)}
$$

To justify the sum, I count zeros of $E_\varepsilon$ in disks and bound how far their arguments can approach the cut. The growth estimate
$|E_\varepsilon(\lambda)|\le C(1+|\lambda|)\exp(2\sqrt{|\lambda|})$ and Jensen's formula
give a zero count $O(\sqrt R)$ in a disk of radius $R$. This gives absolute convergence for $\Re s>1/2$. At a zero $\lambda$, choose the square root $u$ that satisfies equation [(7)](#eq-7). Then
$|u|=\varepsilon|\cos u|\ge\varepsilon\sinh|\Im u|$, hence
$|\Im u|\le\operatorname{asinh}(|u|/\varepsilon)=O(\log|u|)$. Consequently the large $\lambda$
zeros approach the positive-axis sector. The finitely many remaining zeros
stay off the negative axis. This uniform sector control and the absolutely
summable $|\lambda_j|^{-\Re s}$ justify interchange with the Stieltjes integral.
The determinant and principal-cut
Stieltjes identity give, initially for $1/2<\Re s<1$,

$$
\mathcal Z(s;\varepsilon)
=\frac{\sin\pi s}{\pi}
\int_0^\infty t^{-s}\frac d{dt}\log E_\varepsilon(-t)dt.
$$

On the integration ray, I divide $E_\varepsilon(-t)$ by the determinant of the double half-integer reference spectrum. This gives an exact factorization.

$$
E_\varepsilon(-t)=\cosh^2\sqrt t
\left(1+\frac{t\,\operatorname{sech}^2\sqrt t}{\varepsilon^2}\right).
$$

The $\cosh^2\sqrt t$ factor has the double reference spectrum
$[(n+1/2)\pi]^2$ for $n\ge0$. Since $n+1/2=(2n+1)/2$, the inverse powers of these eigenvalues sum to
$2\pi^{-2s}2^{2s}$ times the sum of the inverse $2s$-powers of the odd integers.
Removing the even terms from $\zeta(2s)$ gives the factor $2^{2s}-1$ in [(21)](#eq-21).
The logarithmic derivative of the quotient accounts for the change from the reference spectrum to the coupled spectrum. Integrating that term by parts gives the correction $J(s;\varepsilon)$.

<a name="eq-21"></a>

$$
\boxed{\mathcal Z(s;\varepsilon)
=2\pi^{-2s}(2^{2s}-1)\zeta(2s)+J(s;\varepsilon),}
\qquad\text{(21)}
$$

<a name="eq-22"></a>

$$
\boxed{J(s;\varepsilon)=\frac{s\sin\pi s}{\pi}
\int_0^\infty t^{-s-1}
\log\left(1+\frac{t\,\operatorname{sech}^2\sqrt t}{\varepsilon^2}\right)dt.}
\qquad\text{(22)}
$$

The integral in [(22)](#eq-22) converges throughout $\Re s<1$. At infinity its integrand
decays exponentially in $\sqrt t$. At zero the logarithm $F(t)$ in [(22)](#eq-22) has a convergent
Taylor series $\sum_{m\ge 1}c_m t^m$. Splitting at any sufficiently small $a>0$
and subtracting its first $M$ terms gives

<a name="eq-23"></a>

$$
\int_0^a t^{-s-1}\left(F(t)-\sum_{m=1}^Mc_mt^m\right)dt
+\sum_{m=1}^M\frac{c_ma^{m-s}}{m-s}
+\int_a^\infty t^{-s-1}F(t)dt.
\qquad\text{(23)}
$$

This continues the integral to $\Re s<M+1$ with simple possible poles at the
positive integers. The factor $\sin(\pi s)$ cancels each pole. Thus $J$ is entire.
This is the endpoint-subtraction Mellin method of
[NIST DLMF §2.5](https://dlmf.nist.gov/2.5), applied here to the displayed
relative determinant.

**Corollary.** The following identities hold for every $\varepsilon>0$.

$$
\boxed{\operatorname*{Res}_{s=1/2}\mathcal Z(s;\varepsilon)=1/\pi,}
$$

$$
\boxed{\mathcal Z(-m;\varepsilon)=0\quad(m=0,1,2,\ldots),}
$$

<a name="eq-24"></a>

$$
\boxed{\mathcal Z'(0;\varepsilon)=-\log4,
\qquad\det{}_\zeta(\mathcal A_\varepsilon^2)=4.}
\qquad\text{(24)}
$$

Indeed the reference zeta has its single pole at $1/2$ and zeros at the
nonpositive integers. For the latter, $\sin(\pi s)$ vanishes in the convergent
relative integral. At zero $J$ has a double zero. The reference derivative is
$2[2\log(2)\zeta(0)]=-\log(4)$. In particular the regularized determinant is
constant along this coupling family even while its individual eigenvalues move.
For shifts $\lambda$ near zero with consistent spectral cuts, the zeta determinant
is therefore $4E_\varepsilon(\lambda)$, and this expression continues it as an
entire determinant in $\lambda$.

An additional computable relative invariant is

<a name="eq-25"></a>

$$
\partial_s^2J(0;\varepsilon)=
2\int_0^\infty\frac1t
\log\left(1+\frac{t\,\operatorname{sech}^2\sqrt t}{\varepsilon^2}\right)dt>0.
\qquad\text{(25)}
$$

At unit coupling, Lean’s **UnitSpectrum.root_hasSum** identifies the actual principal-power series with the continued expression on $1/2<\Re s<1$. **UnitSpectrum.continuation_analytic** proves analyticity when $2s\ne1$. In $0<\Re s<1/2$, **UnitSpectrum.equality_iff_riemann_zero** identifies the equality of the continued sum and the correction with $\zeta(2s)=0$, and **UnitSpectrum.difference_order** proves equality of the orders of vanishing. For the real inverse squared coupling $q=\varepsilon^{-2}\ge0$, **regularized_determinant** evaluates the exponential of the negative derivative at zero of the continued scalar expression in [(24)](#eq-24).
[Root sum, continuation and orders](../../lean/SuperZeta/UnitSpectrum.lean#L34-L75) · [Scalar derivative and regularized determinant](../../lean/SuperZeta/SpecialValues.lean#L46-L66) · [Lean build instructions](../../lean/README.md#run-the-proofs)

### Holomorphic complex coupling domain

Equations [(21)](#eq-21)–[(24)](#eq-24) extend jointly to all complex couplings
$\Re\varepsilon>0$. For $c=t\operatorname{sech}^2\sqrt t\ge0$, the argument
$1+c/\varepsilon^2$ reaches the nonpositive real axis only at purely imaginary
$\varepsilon$. Its principal logarithm is consequently holomorphic throughout the
right half-plane. The Taylor subtraction at zero and exponential tail bounds
are uniform on its compact subsets. Also, $E_\varepsilon(-t)=0$ would force
$\varepsilon^2=-t/\cosh^2\sqrt t$, again purely imaginary $\varepsilon$. The spectral cut
and the Jensen/sector estimates above remain valid uniformly on coupling
compacts. Thus the displayed function is jointly meromorphic in $s$ and
holomorphic in the complex coupling, and its zeta determinant remains 4.
The strict positivity in [(25)](#eq-25) concerns real $\varepsilon>0$. Directed numerical
examples in this package use the real couplings one and two.
The right half-plane result follows from the written branch argument. The purely imaginary axis can meet the cut when $\varepsilon^2=-c$ for some $c=t\operatorname{sech}^2\sqrt t$ with $t>0$.

## 6. Exact relation to the 2024 inverse-function frontier

The coupling [(7)](#eq-7) is generalized cosine inversion, $\varepsilon=u\sec u$. Stoutemyer studies the real inverse branches of $\cos u=c_0u$ with $c_0=1/\varepsilon$, equivalently $y_0(u)=-1/\varepsilon$. In the $\alpha$-plane I use the auxiliary deformation below.
[Stoutemyer (2024), §2.4, eq. (13)](https://mapletransactions.org/index.php/maple/article/download/16787/16573/55313#page=10)

$$
\alpha^2\exp(\varepsilon(\alpha-\alpha^{-1}))=-1,
\qquad u=\varepsilon(\alpha-\alpha^{-1})/(2i).
$$

At $\varepsilon=1$ it recovers the original reciprocal parabolic spectrum.
The spectral zeta and boundary operator extend the analytic structure of
that inverse-function family.

Its critical equation is exactly

$$
\frac{d\varepsilon}{du}=\sec u(1+u\tan u)=0.
$$

On $u=iv$ this gives $v\tanh v=1$ and the Laplace critical value
$\varepsilon=iv/\cosh v$. Thus the earlier inverse-Bessel/Kepler fold is also
the multiple-eigenvalue locus of the characteristic equation [(7)](#eq-7).
Stoutemyer gives the Laplace limit in his elliptic Kepler discussion. On the positive imaginary coupling axis, that limit is the magnitude of the coupling at the boundary eigenvalue collision in [(7)](#eq-7).
[Stoutemyer (2024), §4.2](https://mapletransactions.org/index.php/maple/article/download/16787/16573/55313#page=19)

In the companion approximation work I use Borghi’s positive Stieltjes representation for the complex Kapteyn series of elliptic Kepler’s equation. The companion note transfers that measure into bounds for the reciprocal fixed phases. In §5 above the Stieltjes integral instead uses the resolvents of the squared cosine roots.
[Borghi (2024), eqs. (15)–(17), (23), and (26)](https://www.mdpi.com/2227-7390/12/1/154) · [Padé transfer and its interval enclosures](../../archive/2026-11-18-lean-foundations-v001/notes/pade-transfer.md)

## Reproducible checks

`computations/verify_cosine_spectrum.py` retains exact trace polynomials,
finite-matrix determinant checks, directed finite-projection error bounds,
phase/parameter recovery checks, canonical-product tails, and directed Mellin
integral evaluations. Working precisions and every numerical scope are recorded
in `computations/cosine-spectrum-results.json`.

The [runnable copy of the original verifier](../../archive/2026-11-18-spectral-reproduction-v001/verify_cosine_spectrum.py)
writes its output beside the script. Follow the [scratch replay instructions](../../archive/2026-11-18-spectral-reproduction-v001/README.md#run-from-a-fresh-checkout)
and compare with the [deposited results](../../archive/2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum-results.json).

A separately written FLINT ball-arithmetic check evaluates the full logarithmic derivative integral and, separately, the relative integral plus the double half-integer reference at $s=(3+i)/4$ and $\varepsilon=1$. At 192 bits their difference ball contains zero and bounds both component magnitudes by $2	imes10^{-20}$, including both omitted tails. This tests the two formulas at one nonreal argument. The original verifier’s real-coupling examples use $\varepsilon=1,2$.
[Two-integral verifier](../../archive/2026-11-18-spectral-reproduction-v001/check_complex_mellin.py) · [Archived enclosure and replay scope](../../archive/2026-11-18-spectral-reproduction-v001/README.md#the-mellin-integral-and-its-branch)
