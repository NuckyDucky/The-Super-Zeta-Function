# Balanced histories have a primitive Euler product and retain parabolic order

16 November 2026. The central-binomial probabilities admit an exact
primitive-history zeta. Retaining the actual ordered exponential operations
then supplies a finite formula for a parabolic germ invariant and a certified
four-stage example whose sign differs from the alternating Dottie germ.

## 1. The operators retain every arrangement

Let
\[
E_s(z)=e^{sLz},\qquad s\in\{1,-1\},\quad L\ne0.
\]
For a **forward** word \(w=(s_1,\ldots,s_m)\), set
\[
z_{j+1}=E_{s_{j+1}}(z_j),\qquad
F_w=E_{s_m}\circ\cdots\circ E_{s_1}.
\tag{1}
\]
A balanced history has \(m=2n\), with n occurrences of each sign.
There are \(a_n=\binom{2n}{n}\) such ordered words.

For an entire test function f define the continuous composition operators
\(C_s f=f\circ E_s\). The Laurent-polynomial operator
\[
\mathcal T(x)=xC_++x^{-1}C_-
\]
has the exact charge-zero projection
\[
\boxed{[x^0]\mathcal T(x)^{2n}
=\sum_{w\ {\rm balanced}}C_{s_1}\cdots C_{s_{2n}},}
\tag{2}
\]
and the term on the right acts as \(f\mapsto f\circ F_w\), with the
forward order (1). The scalar augmentation \(C_s\mapsto1\) gives the
central-binomial count. The operator expression retains every arrangement.

Order already appears in the first balanced degree. Applied to
\(f(z)=z\), the commutator satisfies
\[
\boxed{([C_+,C_-]f)(0)=e^{-L}-e^L=-2\sinh L.}
\tag{3}
\]
At the Dottie parameter \(L=iy_*\), this is \(-2i\sin y_*\ne0\).

For two independent streams, use
\(\mathcal T(x)\otimes\mathcal T(y)\) and take the simultaneous
constant term. The scalar count is
\(\binom{2n}{n}^2\), and dividing by \(4^{2n}=16^n\) gives exactly
\[
B_n^2=\frac{\binom{2n}{n}^2}{16^n}.
\tag{4}
\]
The accompanying lattice/charge operator realization is developed in
[the charge-operator note](balanced-charge-operators.md).

## 2. Primitive balanced histories give an exact Euler product

A primitive word is not a proper power. A necklace identifies words under
cyclic rotation, with the order and both sign labels retained. Let
\(P_n^{(r)}\) count primitive balanced necklaces of length \(2n\) for
\(r=1\) or \(r=2\) independent simultaneous streams. Then
\[
\boxed{P_n^{(r)}=\frac1{2n}\sum_{d\mid n}\mu(d)
\binom{2n/d}{n/d}^{r}.}
\tag{5}
\]
Here cyclic rotation acts simultaneously on both streams when \(r=2\).

**Proof.** A power \(v^d\) is balanced precisely when its primitive root
v is balanced, since each integer charge is multiplied by d. The root
length is therefore \(2n/d\), with \(d\mid n\). A primitive necklace
of root length \(2k\) has \(2k\) distinct rooted words, so
\[
\binom{2n}{n}^r=\sum_{k\mid n}2kP_k^{(r)}.
\]
Möbius inversion proves (5). ∎

It follows that the complete balanced-history zeta is the exact formal
Euler product
\[
\boxed{\mathcal Z_r(q)
=\exp\left(\sum_{n\ge1}\frac{\binom{2n}{n}^r}{2n}q^n\right)
=\prod_{n\ge1}(1-q^n)^{-P_n^{(r)}}.}
\tag{6}
\]
The variable q marks **half the number of individual operations**. Its
analytic disk is \(|q|<4^{-r}\). Every exponent is a nonnegative integer
because it counts the primitive necklaces in (5).

The first values are:

| n | one stream \(P_n^{(1)}\) | two streams \(P_n^{(2)}\) |
|---:|---:|---:|
|1|1|2|
|2|1|8|
|3|3|66|
|4|8|608|
|5|25|6350|
|6|75|71112|

This is the balanced multigraded version of the classical necklace/Witt
construction. The one-stream number is also the dimension of the
\((n,n)\) component of the free Lie algebra on two formal generators.
Indeed the multigraded Poincaré–Birkhoff–Witt identity is
\(1/(1-x-y)=\prod_{a,b}(1-x^ay^b)^{-\ell_{a,b}}\).
Taking logarithms and the coefficient of \(x^ny^n\) gives
\(\binom{2n}{n}/(2n)=\sum_{d\mid n}\ell_{n/d,n/d}/d\);
Möbius inversion identifies \(\ell_{n,n}\) with (5).
The elementary word proof above directly establishes the enumeration used here.
For the surrounding necklace algebra and its Frobenius/Verschiebung
structures, see [Lenart's primary research paper, §1](https://fpsac-archive.github.io/FPSAC96/ARTICLES/32Lenart.pdf),
which credits the Metropolis–Rota necklace algebra. The formal generators
map to the actual composition operators in (2); their first balanced
commutator is realized explicitly in (3).

For one stream,
\[
\boxed{\mathcal Z_1(q)=\frac2{1+\sqrt{1-4q}},}
\tag{7}
\]
the Catalan generating function. This follows by differentiating the
logarithm of (7) and using
\(\sum_{n\ge0}\binom{2n}{n}q^n=(1-4q)^{-1/2}\), then checking the
value 1 at zero.

## 3. The two-stream zeta has a complete elliptic derivative

Normalize the two-stream zeta by
\[
\widehat{\mathcal Z}_2(t):=\mathcal Z_2(t/16)
=\exp\left(\frac12\sum_{n\ge1}\frac{B_n^2}{n}t^n\right),
\quad |t|<1.
\tag{8}
\]
Use the **parameter** convention
\[
\mathbf K(t)=\int_0^{\pi/2}\frac{d\theta}
{\sqrt{1-t\sin^2\theta}}.
\]
Thus \(\mathbf K(t)\) is the DLMF modulus-convention function
\(K(\sqrt t)\). The central-binomial hypergeometric series gives
\[
\sum_{n\ge0}B_n^2t^n
={}_2F_1(\tfrac12,\tfrac12;1;t)=\frac2\pi\mathbf K(t),
\]
as in [NIST DLMF 19.5.1](https://dlmf.nist.gov/19.5.E1), with that
modulus/parameter conversion. Therefore
\[
\boxed{t\frac d{dt}\log\widehat{\mathcal Z}_2(t)
=\frac{\mathbf K(t)}\pi-\frac12.}
\tag{9}
\]
The Green function and the primitive-history determinant are linked by one
logarithmic integration, while the history lengths and normalization remain
explicit.

There is also an exact critical value. Let
\(G_{\rm Cat}=\sum_{k\ge0}(-1)^k/(2k+1)^2\). Then
\[
\boxed{\widehat{\mathcal Z}_2(1)
=4e^{-4G_{\rm Cat}/\pi}
=1.24613996435124212468678373589735173173848\ldots.}
\tag{10}
\]

**Proof.** The normalized simultaneous step symbol is
\(a(\theta,\phi)=\cos\theta\cos\phi\). Its odd torus moments vanish,
and its \(2n\)-th moment is \(B_n^2\). For \(0\le t<1\), expand the
logarithm to obtain
\[
\log\widehat{\mathcal Z}_2(t)
=-\frac1{(2\pi)^2}\int_0^{2\pi}\int_0^{2\pi}
\log(1-\sqrt t\cos\theta\cos\phi)\,d\theta\,d\phi.
\tag{11}
\]
The critical logarithmic singularities are integrable. At \(t=1\),
integrating in \(\phi\) gives
\[
I:=\frac1{(2\pi)^2}\iint\log(1-\cos\theta\cos\phi)
=\frac2\pi\int_0^{\pi/2}\log\frac{1+\sin\theta}{2}\,d\theta.
\]
Since \((1+\sin\theta)/2=\sin^2(\theta/2+\pi/4)\),
\[
I=\frac8\pi\int_{\pi/4}^{\pi/2}\log\sin u\,du
=-2\log2+\frac4\pi G_{\rm Cat}.
\]
The last integral follows by integrating the Fourier series for
\(\log(2\sin u)\), or by the defining odd-square series for Catalan's
constant. Taking \(e^{-I}\) proves (10). ∎

This critical constant is the normalized square-lattice determinant
constant. The underlying square-lattice spanning-tree entropy
\(4G_{\rm Cat}/\pi\) is classical; see
[Viswanathan, §II, equations (4)–(5), with the earlier Wu reference](https://arxiv.org/pdf/1706.00799).
Here it enters through the exact primitive balanced-history construction.

## 4. A cyclic periodic history has an exact action and multiplier

Now retain an actual periodic phase history satisfying (1) and
\(z_m=z_0\). Define the partial derivatives and actual lifted logarithms
\[
D_0=1,\qquad D_j=\prod_{k=1}^j s_kLz_k,
\]
\[
U_j=s_{j+1}Lz_j,\quad e^{U_j}=z_{j+1},\qquad
\mathcal A_w=\sum_{j=0}^{m-1}U_j.
\tag{12}
\]
The logarithms in (12) are supplied by the actual exponential arguments;
they retain their lifts. The multiplier of the return is
\[
\boxed{\mu_w=D_m=L^m\left(\prod_{k=1}^ms_k\right)e^{\mathcal A_w}.}
\tag{13}
\]
This follows by multiplying the derivatives
\(E_{s_k}'(z_{k-1})=s_kLz_k\) and using
\(\prod z_k=e^{\sum U_j}\).

For a balanced word of length \(2n\) at \(L=iy\), \(y>0\), equation
(13) simplifies exactly to
\[
\boxed{\mu_w=y^{2n}e^{\mathcal A_w}.}
\tag{14}
\]
Thus every multiplier-one balanced periodic phase history satisfies
\[
\boxed{\mathcal A_w=-2n\log y+2\pi i k,\qquad k\in\mathbb Z.}
\tag{15}
\]
This gives a lifted integer invariant as well as the combinatorial balance.
Both \(\mathcal A_w\) and k are unchanged when the phase origin and the
word are cyclically rotated together.

Cyclic necklaces are also the natural labels for local return germs.
Let \(A=E_{s_1}\) and \(B=E_{s_m}\circ\cdots\circ E_{s_2}\), so
\(F_w=B\circ A\) and its one-step rotation has return \(A\circ B\).
On their fixed sets, A and B are mutual inverse bijections. Since
\(A'\ne0\), A is a local holomorphic conjugacy at corresponding fixed
points. Hence every local germ invariant, including the multiplier and the
simple-parabolic iterative residue, is retained under that cyclic rotation.

## 5. An arrangement-sensitive parabolic invariant in finite phase data

**Theorem.** Suppose the return of a signed periodic phase history is simple
parabolic at \(z_0\). Retain the forward signs and \(D_j\) in (12), and
put
\[
S_1=\sum_{j=0}^{m-1}s_{j+1}D_j,\qquad
S_2=\sum_{j=0}^{m-1}D_j^2.
\]
Then the quadratic coefficient and iterative residue are
\[
\boxed{a_w=\frac{L}{2}S_1,\qquad
\rho_w=\frac{S_2}{3S_1^2}.}
\tag{16}
\]
Here \(F_w(z_0+\xi)=z_0+\xi+a_w\xi^2+b_w\xi^3+\cdots\), and
\(\rho_w=1-b_w/a_w^2\). The simple-parabolic condition is \(S_1\ne0\).

**Proof.** Each signed exponential satisfies
\[
\frac{E_s''}{E_s'}=sL,\qquad
\operatorname{Sch}(E_s)=-\frac{L^2}{2},
\]
where
\(\operatorname{Sch}(f)=f'''/f'-\tfrac32(f''/f')^2\).
The logarithmic-derivative and Schwarzian chain rules give
\[
\frac{F_w''}{F_w'}=LS_1,\qquad
\operatorname{Sch}(F_w)=-\frac{L^2}{2}S_2.
\]
At multiplier one, \(F_w'=1\), so
\[
a_w=LS_1/2,\qquad
b_w=a_w^2-L^2S_2/12.
\]
Substituting in the definition of \(\rho_w\) gives (16). ∎

There is a direct cyclic check of (16). Extend the partial derivatives
periodically using \(D_m=1\). Rotation by j scales every new partial
derivative by \(D_j^{-1}\). Thus \(S_1\) scales by \(D_j^{-1}\),
\(S_2\) by \(D_j^{-2}\), and their quotient in (16) is invariant.

For the original alternating Dottie return, choose the forward word
\((-1,+1)\), starting at P. Then \(D_0=1,D_1=-\alpha\), with
\(\alpha=s_d+id\), giving
\[
\rho_D=\frac{1+\alpha^2}{3(1+\alpha)^2}
=\frac{s_d}{3(1+s_d)}.
\tag{17}
\]
The equality follows from \(\alpha^2-2s_d\alpha+1=0\).
It recovers the existing normalized Dottie invariant directly from the
general signed-history formula.

## 6. Complementary halves produce exact antiholomorphic roots

For pure imaginary L let \(J(z)=\bar z\). Then
\(E_{-s}=J\circ E_s\circ J\). If \(-v\) denotes sign complement
without reversing the order, then
\[
F_{-v}=J\circ F_v\circ J.
\]
The balanced forward word \(w=v(-v)\) therefore satisfies
\[
\boxed{F_w=F_{-v}\circ F_v=(J\circ F_v)^2.}
\tag{18}
\]
This supplies an actual antiholomorphic half-return for every history with
complementary halves. The original alternating word is the case where v
has one sign. The primitive four-stage word \((+,+,-,-)\) is the case
\(v=(+,+)\).

These words have a separate exact primitive count. Let \(A_n\) be the
number of primitive necklaces of length \(2n\) satisfying
\(s_{j+n}=-s_j\). Then
\[
\boxed{A_n=\frac1{2n}\sum_{\substack{d\mid n\\d\ {\rm odd}}}
\mu(d)2^{n/d}.}
\tag{19}
\]
To prove it, there are \(2^n\) rooted complementary-half words. A balanced
primitive root of length \(2k\) can repeat \(n/k\) times here only when
that repetition count is odd; an even count would make the half-turn fix
the sign. Its primitive root is itself a complementary-half word.
Therefore \(2^n=\sum_{d\mid n,\ d\text{ odd}}2(n/d)A_{n/d}\), and
odd-divisor Möbius inversion gives (19). This retains the dyadic index
of n explicitly. The first values are \(1,1,1,2,3,5,9,16\).

## 7. A certified primitive four-stage fold has negative residue

There exists a unique solution in the retained real box of radius
\(10^{-140}\) around
\[
\begin{aligned}
y={}&0.75019697231646184963089152468402761224048355950409529934\ldots,\\
z_0={}&0.09081518944588625089726158747837491331981804581735773909\ldots\\
&-0.89997673217325701299210518067923462630447592477815982733\ldots\,i
\end{aligned}
\tag{20}
\]
such that \(K_y=J\circ E_+^2\) fixes \(z_0\) and
\(|(E_+^2)'(z_0)|=1\), with \(L=iy\). Thus
\[
F_{++--}=E_-^2\circ E_+^2=K_y^2
\]
has a simple parabolic fixed point. This is a fixed point of the four-stage
return; the forward signed history is primitive and its four stage phases
are distinct:
\[
\begin{aligned}
z_0&=0.09081518944588625-0.89997673217325701i+\cdots,\\
z_1&=1.95978980006906823+0.13372603326638104i+\cdots,\\
z_2&=\bar z_0,\qquad z_3=\bar z_1.
\end{aligned}
\]
The local antiholomorphic diffeomorphism \(K_y\) fixes \(z_0\) and commutes
with \(F_{++--}=K_y^2\). It therefore antiholomorphically conjugates that
return germ to itself. The holomorphic conjugacy invariant \(\rho\) is
complex-conjugated by an antiholomorphic change of coordinate, so
\(\rho_{++--}=\bar\rho_{++--}\) exactly. Its real value is enclosed by
\[
\boxed{\rho_{++--}=-0.01987482392764093278654835457977383761597300\ldots<0.}
\tag{21}
\]
All four cyclic origins give the same invariant. The lifted action is real
and equals \(-4\log y\), so the integer in (15) is zero.

For comparison, the equal-count alternating history \((+,-,+,-)\) at the
Dottie parameter is a second iterate of its two-stage return. If
\(f(\xi)=\xi+a\xi^2+b\xi^3+\cdots\), then
\(f^2=\xi+2a\xi^2+(2b+2a^2)\xi^3+\cdots\), so
\(\rho(f^2)=\rho(f)/2\). Consequently,
\[
\boxed{\rho_{+-+-}=\frac{\sin d}{6(1+\sin d)}>0.}
\tag{22}
\]
The two histories both contain two operations of each sign; their
simple-parabolic return germs have opposite-sign iterative residues.
Equations (1), (18), and (20) retain the actual return and parameter used
for each history.

### Three-variable existence and uniqueness certificate

Here are all analytic functions used in the certificate. Write
\(z=x+it\), \(L=iy\),
\[
a=e^{Lz},\qquad b=e^{La},\qquad d_1=L^2ab=(E_+^2)'(z).
\]
The real system is
\[
f(x,t,y)=(\Re b-x,\ \Im b+t,\ |d_1|^2-1)=0.
\tag{23}
\]
For its exact analytic Jacobian, put
\[
h_y=iab(1+Lz),\quad
d_z=d_1L(1+La),\quad
d_y=d_1\{2/y+iz+ia(1+Lz)\}.
\]
Then
\[
Df=\begin{pmatrix}
\Re d_1-1&-\Im d_1&\Re h_y\\
\Im d_1&\Re d_1+1&\Im h_y\\
2\Re(\bar d_1d_z)&2\Re(i\bar d_1d_z)&2\Re(\bar d_1d_y)
\end{pmatrix}.
\tag{24}
\]

The script retains exact decimal-rational centers of 180 digits and the
real box \(X=c+[-r,r]^3\), \(r=10^{-140}\). Let A be the retained
180-digit rational approximation to \(Df(c)^{-1}\). Directed 1024-bit
evaluation proves
\[
\|I-A Df(X)\|_\infty<2.79\times10^{-138},\qquad
\|Af(c)\|_\infty<4.15\times10^{-181}.
\]
The stronger entrywise sum is used to bound the first norm, so interval
maximum comparisons are unnecessary. These bounds prove
\[
\|Af(c)\|_\infty+r\|I-A Df(X)\|_\infty<r.
\]
The map \(v\mapsto v-Af(v)\) is a strict contraction of X into itself.
It has exactly one fixed point there. The matrix A is invertible because
\(\|I-A Df(c)\|<1\); hence that fixed point solves (23).

The same box proves that every pair of stage phases has distance greater
than \(0.1\), that the quadratic factor \(S_1\) is nonzero, and that
the residue in (21) is strictly negative. The return multiplier, action,
and all cyclic residues are evaluated with directed balls. Independent
220-digit differentiation checks the full three-variable Jacobian and
the second and third derivatives of the actual fourfold composition.

## 8. Reproduction and interpretation

`computations/verify_signed_histories.py` and its JSON record establish:

- Exact primitive counts through n=12, with direct necklace enumeration
  through n=6 for one stream, n=4 for two streams, and n=8 for complementary
  halves.
- Exact agreement of the logarithmic series and primitive Euler products
  through degree 12, including the Catalan formula for one stream.
- The critical constant (10), checked by directed bounds on 4096 terms
  and independent 220-digit log-sine integration.
- The three-variable fold certificate, four distinct stage phases,
  multiplier one, nonzero quadratic coefficient, negative residue,
  lifted action, cyclic invariance, and the positive alternating
  equal-count comparison.

For the critical series check, induction using
\(B_{n+1}/B_n=(2n+1)/(2n+2)\) gives
\(B_n^2\le1/(3n+1)\). Thus the log-series tail at criticality is bounded
by \(\sum_{n>N}1/(6n^2)\le1/(6N)\). The numerical integral checks the
closed constant independently of this slowly convergent positive series.

The complete verifier takes about 0.16 seconds on the current CPU, with
1024-bit directed arithmetic and independent 220-digit point calculations.
Every retained file is inside the new Greater Works Super Zeta package.

The scalar zeta counts every balanced arrangement and separates its
primitive cyclic histories. The operator projection (2) retains the
actual exponential order. The finite phase formula (16) then evaluates
how that order appears in a local parabolic germ. These are explicit
transitions between the central-binomial probabilities, primitive Euler
factors, and NuckyDucky's reciprocal-exponential dynamics.
