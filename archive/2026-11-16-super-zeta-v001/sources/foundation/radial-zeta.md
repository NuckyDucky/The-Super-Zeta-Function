# The quartet radii form a meromorphic spectral zeta

16 November 2026. Direct analytic continuation, complete pole classification,
an explicit uniform truncation bound, and a regularized radial product.

The input is NuckyDucky's complete multiplier-one fixed-pair classification. Put
\[
\theta(t)=\arccos\!\left(-\frac{t}{\sinh t}\right),\qquad
F(t)=\theta(t)+\cosh t\sin\theta(t).
\]
For every integer \(n\ge1\), the unique positive solution of
\[
F(t_n)=(n+\tfrac12)\pi
\]
gives one parameter quartet of common radius
\[
R_n=\exp(t_n\coth t_n).
\]
The earlier proof establishes \(F'>0\), the exact quartet symmetries and
\(R_n\sim2\pi n\). Here this sequence becomes an analytic spectrum.

## 1. The radial zeta theorem

Define
\[
\boxed{Z_R(s)=\sum_{n\ge1}R_n^{-s},\qquad\Re s>1,}
\tag{1}
\]
using the real logarithm of each positive \(R_n\).

**Theorem.** The following statements hold.

1. \(Z_R\) continues meromorphically to the whole complex plane. Its poles
   are exactly
   \[
   \boxed{s_j=1-2j,\qquad j=0,1,2,\ldots.}
   \]
   The pole at \(s_j\) has order \(2j+1\).
2. At \(s=1\), the residue is \(1/(2\pi)\). At \(s=-1\), the entire
   principal part is
   \[
   \boxed{\frac{2/\pi}{(s+1)^3}
   -\frac{3/\pi}{(s+1)^2}+\frac{1/(2\pi)}{s+1}.}
   \tag{2}
   \]
   At every \(s_j\), the highest Laurent coefficient is
   \[
   \boxed{\frac{((2j)!)^2}{2\pi(j!)^2}.}
   \tag{3}
   \]
   The residues at \(-3,-5,-7,\ldots\) are all zero, even though these
   points have poles of orders \(5,7,9,\ldots\).
3. At zero,
   \[
   \boxed{Z_R(0)=-\tfrac12,\qquad
   e^{-Z_R'(0)}=\prod_{n\ge1}\frac{R_n}{2\pi n}.}
   \tag{4}
   \]
   The product on the right converges absolutely after taking real
   logarithms, and its value is exactly
   \[
   \boxed{\mathcal P=e^{\sin d/2},\qquad Z_R'(0)=-\sin d/2,
   \qquad d=\cos d.}
   \tag{4a}
   \]
4. The radial canonical product
   \[
   \boxed{\mathcal D_R(z)=\prod_{n\ge1}(1-z^2/R_n^2)}
   \tag{5}
   \]
   is an even entire function of order one and exponential type \(1/2\).
   Its normalization at imaginary infinity is
   \[
   \boxed{\mathcal D_R(iy)\sim\mathcal P^{-2}\frac{e^{y/2}}{y}
   =e^{-\sin d}\frac{e^{y/2}}y
   \qquad(y\to+\infty).}
   \tag{6}
   \]

This is also a literal spectral zeta: on \(\ell^2(\mathbb N)\), the
positive self-adjoint operator
\[
T_R e_n=R_n e_n,\qquad
\operatorname{Dom}(T_R)=\{a:\sum R_n^2|a_n|^2<\infty\}
\]
has compact resolvent and \(\operatorname{Tr}(T_R^{-s})=Z_R(s)\) in (1).
The radial observable records one level per quartet. Fourfold parameter
multiplicity and the Dottie pair are restored explicitly in Section 7.

## 2. The exact smooth counting coordinate

Set
\[
A(t)=2F(t)-\pi,
\qquad R(t)=e^{t\coth t},\qquad \ell=\log R.
\]
Then \(A(t_n)=2\pi n\), and both coordinates increase for \(t>0\).
The identity \(\theta=\pi/2+\arcsin(t/\sinh t)\) gives
\[
A(t)=2\arcsin(t/\sinh t)
 +2\cosh t\sqrt{1-(t/\sinh t)^2}.
\tag{7}
\]
For \(r=e^t\) and \(z=r^{-2}\), define the analytic expression
\[
H(t,z)=(1+z)\sqrt{1-\frac{4t^2z}{(1-z)^2}}
 +2\sqrt z\,\arcsin\!\left(\frac{2t\sqrt z}{1-z}\right).
\tag{8}
\]
The second term has an ordinary power series in \(z\); the two square
roots cancel its apparent half-integer powers. All branches in (8) are
the germs equal to their usual real values at \(z=0\). Equation (7) is
exactly \(A=rH(t,r^{-2})\).

Now use \(x=R^{-2}\) and \(\delta=t-\ell\). Since
\(\ell=t\coth t\), the inverse equation simplifies to
\[
\boxed{\delta=-x(2\ell+\delta)e^{-2\delta}.}
\tag{9}
\]
For fixed \(\ell\), it has a unique analytic solution near \(x=0\),
with \(\delta(\ell,0)=0\). Lagrange inversion gives its coefficients
explicitly:
\[
[x^j]\delta=
\frac{(-1)^j}{j}
\sum_{a=0}^{j-1}\binom ja(2\ell)^{j-a}
\frac{(-2j)^{j-1-a}}{(j-1-a)!}.
\tag{10}
\]
In particular these are rational polynomials of degree at most \(j\).

Substitute (9) into
\[
\boxed{M(\ell,x)=e^\delta
 H(\ell+\delta,xe^{-2\delta}).}
\tag{11}
\]
For real large \(R\), this is exactly \(A(R)/R\). Thus
\[
\frac{A(R)}R=1+\sum_{j\ge1}Q_j(\log R)R^{-2j}.
\tag{12}
\]
The series is convergent in the two-variable disks justified in Section 5;
as \(R\to\infty\), it is a uniform all-order logarithmic asymptotic
expansion. Its first terms are
\[
Q_1(\ell)=-2\ell^2+2\ell+1,
\]
\[
Q_2(\ell)=-2\ell^4-\tfrac43\ell^3+4\ell^2,
\]
\[
Q_3(\ell)=-4\ell^6-\tfrac{36}5\ell^5+2\ell^4
 +\tfrac{44}3\ell^3-4\ell^2.
\]
Every \(Q_j\) is rational, with degree \(2j\). Its leading coefficient is
\[
[\ell^{2j}]Q_j=(-4)^j\binom{1/2}{j}.
\tag{13}
\]
Indeed an additional power of \(x\) in \(\delta\) increases polynomial
degree by at most one. At order \(x^j\), only the \(j\)-th radical term
in (8) can have degree \(2j\). The arcsine terms have degree at most
\(2j-1\). This proves (13), including its nonvanishing.

## 3. The density determines every principal part

Differentiating (12) gives
\[
A'(R)=1+\sum_{j\ge1}D_j(\log R)R^{-2j},
\qquad
\boxed{D_j=(1-2j)Q_j+Q_j'.}
\tag{14}
\]
The first three density polynomials are
\[
D_1=2\ell^2-6\ell+1,
\]
\[
D_2=6\ell^4-4\ell^3-16\ell^2+8\ell,
\]
\[
D_3=20\ell^6+12\ell^5-46\ell^4
 -\tfrac{196}3\ell^3+64\ell^2-8\ell.
\]
Their highest coefficients satisfy the exact all-order identity
\[
\boxed{[\ell^{2j}]D_j=\binom{2j}{j}.}
\tag{15}
\]

The zero residues have a short structural proof. Expand (9) to first order
in \(\ell\), retaining \(x\) as an independent formal variable:
\[
\delta=-\frac{2x}{1+x}\ell+O(\ell^2),
\qquad t=\frac{1-x}{1+x}\ell+O(\ell^2).
\]
Insertion in (11) gives
\[
\boxed{M(\ell,x)=1+x+2x\ell+O(\ell^2).}
\tag{16}
\]
Hence \(Q_1(0)=1\), \(Q_1'(0)=2\), while
\(Q_j(0)=Q_j'(0)=0\) for every \(j\ge2\). Therefore
\[
D_1(0)=1,\qquad \boxed{D_j(0)=0\quad(j\ge2).}
\tag{17}
\]

Here is the precise passage from density to zeta. Extend the index smoothly
by \(n=A(R)/(2\pi)\). Euler–Maclaurin expresses the tail of (1) as
\[
\frac1{2\pi}\int_B^\infty R^{-s}A'(R)\,dR
\]
plus boundary terms entire in \(s\) and a remainder holomorphic in
successively larger left half-planes as more derivatives are included.
The analytic implicit expansions above give, uniformly for \(s\) in
compact sets, \(d^m(R(n)^{-s})/dn^m=O(n^{-\Re s-m})\). For example
this follows by Cauchy's estimate on \(|z-n|<n/2\), where the same
large-index implicit branch is analytic: the disk argument in Section 5
extends to complex logarithmic coordinates by replacing \(1+L\) with
\(1+|L|\) in every majorant. Thus an Euler–Maclaurin remainder
with \(2m\) derivatives is holomorphic for \(\Re s>1-2m\).

Writing \(D_j(\ell)=\sum_{k=0}^{2j}d_{j,k}\ell^k\), the elementary
integrals
\[
\int_B^\infty R^{-s-2j}(\log R)^k\,dR
=(-\partial_s)^k\frac{B^{1-s-2j}}{s+2j-1}
\]
have principal part \(k!/(s-s_j)^{k+1}\). The cutoff \(B\) affects only
their holomorphic parts. Consequently
\[
\boxed{\operatorname{PP}_{s=s_j}Z_R(s)
=\frac1{2\pi}\sum_{k=0}^{2j}
\frac{k!\,d_{j,k}}{(s-s_j)^{k+1}}.}
\tag{18}
\]
Equations (15) and (17) prove the exact pole orders, highest coefficients
and zero-residue statement. For example at \(s=-3\), with \(w=s+3\),
\[
\boxed{\operatorname{PP}_{s=-3}Z_R(s)
=\frac1{2\pi}\left(\frac{144}{w^5}-\frac{24}{w^4}
-\frac{32}{w^3}+\frac8{w^2}\right).}
\tag{19}
\]

The Mellin relationship between logarithmic asymptotics and higher poles is
classical; [NIST DLMF §2.5](https://dlmf.nist.gov/2.5) gives its general
framework. Here the exact density polynomials and the cancellation (16)
are derived from NuckyDucky's radial spectrum.

## 4. A directly evaluable continuation by zeta subtraction

For computation, put \(a_n=2\pi n\), \(L_n=\log a_n\). Invert (12) as
\[
\chi(L,x)=\log(R/A)=\sum_{j\ge1}\chi_j(L)x^j,
\qquad x=A^{-2}.
\]
The first two polynomials are
\[
\chi_1=2L^2-2L-1,
\]
\[
\chi_2=-4L^4+\tfrac{64}3L^3-16L^2-6L+\tfrac12.
\tag{20}
\]
Define the rational-polynomial coefficients
\[
\boxed{C_j(s,L)=[x^j]e^{-s\chi(L,x)},\qquad C_0=1.}
\tag{21}
\]
They satisfy \(\deg_L C_j\le2j\). With
\[
H(s)=(2\pi)^{-s}\zeta(s),
\]
one gets, for every \(J\ge0\),
\[
\boxed{Z_R(s)=\sum_{j=0}^J C_j(s,-\partial_s)H(s+2j)+E_J(s),}
\tag{22}
\]
where the derivative acts on \(H\), holding the displayed polynomial
coefficients in \(s\) fixed, and \(E_J\) is holomorphic for
\(\Re s>-2J-1\). Normal convergence of the subtracted series proves this
assertion directly. In particular
\[
Z_R(s)=H(s)-s\{2H''(s+2)+2H'(s+2)-H(s+2)\}+E_1(s).
\tag{23}
\]
Increasing \(J\) supplies the whole-plane continuation and agrees on
overlaps with the density proof. The Riemann zeta input and its single
simple pole are documented in
[NIST DLMF §25.2](https://dlmf.nist.gov/25.2).

Equation (22) is also an all-order algorithm. The retained exact script
computes the implicit coefficients by (10), constructs (11), reverts the
counting coordinate and exponentiates (21). It verifies the density
principal-part identities through \(j=4\) by exact rational algebra.

## 5. Explicit analytic disks and rigorous numerical tail bounds

The following uniform constant makes the subtraction controlled rather than
only asymptotic. For every real \(L\ge0\), set
\[
\boxed{\rho_L=\frac1{256(1+L)^2}.}
\]
Then the radius-inversion branch \(\chi(L,x)\) is analytic on
\(|x|\le\rho_L\) and obeys
\[
\boxed{|\chi(L,x)|<1/8.}
\tag{24}
\]

### Proof of the uniform disk

On \(|\chi|=1/8\), put \(\lambda=L+\chi\),
\(y=xe^{-2\chi}\), and solve
\[
\delta=-y(2\lambda+\delta)e^{-2\delta}.
\]
On \(|\delta|\le1/8\), its right side has modulus at most
\[
\frac{e^{1/2}}{256}\frac{2L+3/8}{(1+L)^2}
\le\frac{e^{1/2}}{256}\frac8{13}<\frac1{250}.
\]
The derivative in \(\delta\) has modulus at most
\(e^{1/2}(16/9)/256<1/80\). Hence this analytic contraction defines the
unique \(\delta\) there, with \(|\delta|<1/250\).

Let \(t=\lambda+\delta\), \(z=ye^{-2\delta}\). Then
\[
|t|<1+L,\quad |z|<\frac43\rho_L\le\frac1{192},
\quad
\left|\frac{4t^2z}{(1-z)^2}\right|<\frac1{47}.
\]
The square root alone in (8) differs from one by less than \(1/90\); its
modulus is below \(46/45\). The prefactor \(1+z\) contributes at most
\((46/45)/192\) to the difference. The arcsine term has modulus less than
\(1/45\), using
\(|\arcsin w|\le|w|/\sqrt{1-|w|^2}\). It follows that
\[
|H(t,z)-1|<1/25,
\qquad |e^\delta H(t,z)-1|<1/20.
\]
The equation for the radius inverse is
\[
e^\chi M(L+\chi,xe^{-2\chi})=1.
\]
On its \(1/8\)-circle,
\[
|e^\chi-1|\ge\tfrac18(2-e^{1/8})>0.1083,
\]
whereas the perturbation from \(M-1\) is less than
\(e^{1/8}/20<0.0567\). Rouché's theorem gives exactly one root in the
circle, counted with multiplicity. It is simple and analytic in \(x\),
and is the branch \(\chi(L,0)=0\). This proves (24). On the real
large-index section the reconstructed \(t\) is positive, so uniqueness
of \(F(t_n)\) identifies this branch with the actual \(R_n\). ∎

Define the computable decreasing quantity
\[
\eta_N=\frac{256(1+\log(2\pi N))^2}{(2\pi N)^2}.
\]
For \(\eta_N<1\), Cauchy's estimate gives
\[
\left|\chi(L_n,a_n^{-2})-
 \sum_{j=1}^J\chi_j(L_n)a_n^{-2j}\right|
\le\frac18\frac{\eta_n^{J+1}}{1-\eta_n}.
\tag{25}
\]
Consequently the logarithmic product-tail error after \(N\) exact roots
and \(J\) asymptotic terms is at most
\[
\boxed{\frac{256^{J+1}}{8(1-\eta_N)}
 \int_N^\infty\frac{(1+\log(2\pi x))^{2J+2}}
 {(2\pi x)^{2J+2}}\,dx.}
\tag{26}
\]
The monotonicity needed for this integral bound follows by differentiation.

There is a matching bound for the continued zeta. For
\(p=\Re s+2J+2>1\), choose \(N\) with \(\eta_N<1\) and
\(p[1+\log(2\pi N)]\ge2J+2\); the latter condition makes the
integrand below decreasing from \(N\). Replacing the first \(N\) terms by exact values
and the rest by (21) has error at most
\[
\boxed{\frac{e^{|s|/8}\,256^{J+1}}{1-\eta_N}
 \int_N^\infty(1+\log(2\pi x))^{2J+2}(2\pi x)^{-p}\,dx.}
\tag{27}
\]
This follows by applying Cauchy's estimate to \(e^{-s\chi}\) on the
same disk. Every integral here is a finite elementary expression. For
\(k\ge0\), \(p>1\), \(L=1+\log(2\pi N)\),
\[
\int_N^\infty(1+\log(2\pi x))^k(2\pi x)^{-p}\,dx
=(2\pi)^{-p}N^{1-p}
 \sum_{r=0}^k\binom kr\frac{L^{k-r}r!}{(p-1)^{r+1}}.
\tag{28}
\]
The implementation checks every scalar inequality in the disk proof with
directed Arb arithmetic. Hurwitz-zeta Taylor jets evaluate the subtracted
logarithmic moments, so cancellation in the infinite tails is also enclosed.

## 6. Product, determinant and entire-function normalization

The original radius asymptotics imply
\[
\sum_n\left|\log\frac{R_n}{2\pi n}\right|<\infty.
\]
Thus
\(Z_R(s)-H(s)=\sum_n a_n^{-s}(e^{-s\chi_n}-1)\) is holomorphic for
\(\Re s>-1\), vanishes at zero, and has derivative
\(-\sum_n\chi_n\) there. The classical values
\[
\zeta(0)=-1/2,\qquad\zeta'(0)=-\tfrac12\log(2\pi)
\]
give \(H(0)=-1/2\) and \(H'(0)=0\). This proves (4). These two source
values are recorded in
[NIST DLMF §25.6](https://dlmf.nist.gov/25.6).

Normal convergence of (5) follows from \(\sum R_n^{-2}<\infty\).
For \(y>0\), compare it with Euler's hyperbolic-sine product
([NIST DLMF 4.36.1](https://dlmf.nist.gov/4.36.E1)):
\[
\frac{\sinh(y/2)}{y/2}=\prod_{n\ge1}(1+y^2/(2\pi n)^2).
\]
The logarithm of each quotient factor tends to
\(-2\log(R_n/(2\pi n))\) as \(y\to\infty\), and its modulus is
bounded by twice the absolute value of that logarithm. Dominated convergence
therefore proves
\[
\lim_{y\to\infty}
\frac{\mathcal D_R(iy)}{\sinh(y/2)/(y/2)}=\mathcal P^{-2}.
\]
Moreover \(|\mathcal D_R(z)|\le\mathcal D_R(i|z|)\), with equality
at \(z=i|z|\). Hence the maximum modulus has the asymptotic (6), proving
order one and type \(1/2\).

The exact value of \(\mathcal P\) comes from a complementary trace
calculation in [the radial-product trace theorem](radial-product-trace-theorem.md).
Here is its organizing identity. The entire reciprocal quotient
\(\mathcal J\) has zeros \(x_0=2\sin d\), \(x_n,\bar x_n\), with
\(\Re x_n=-2\log R_n\). For the right-half-plane spectrum
\(a_n=-x_n\), its principal-power zeta satisfies
\[
Z_a(-1)=x_0-1.
\]
This follows by taking the \(t^{-1}\) coefficient of
\(\log[\mathcal J(t)/(\mathcal J(0)(1-t/x_0))]\) in its
canonical-product Mellin integral. A complex asymptotic model for the same
trace has value \(-1\) at that point; its normally convergent remainder
is \(4\sum_n\log(R_n/(2\pi n))\). Therefore
\[
2\sin d-1=-1+4\log\mathcal P,
\]
proving (4a). The companion proof states every logarithmic branch,
Mellin-strip condition and remainder estimate. Its independent review is
retained with this package.

## 7. Restoring the complete parameter-modulus spectrum

The two Dottie parameters have radius \(y_*=e^{-\sin d}\). Each
nonunit level has four parameter representatives. The complete modulus zeta
is therefore
\[
\boxed{Z_{|L|}(s)=2e^{s\sin d}+4Z_R(s).}
\tag{29}
\]
It has the same pole locations and orders, with four times every principal
part. Its exact value at zero and regularized determinant are
\[
\boxed{Z_{|L|}(0)=0,\qquad
 e^{-Z_{|L|}'(0)}=e^{-2\sin d}\mathcal P^4=1.}
\tag{30}
\]
The original four phases are generated by reciprocation and conjugation;
equal moduli place their radial spectral weight in the invariant symmetry
component. The companion phase determinants retain the directions and
phase-coordinate information. This explains why their zeta singularities
can differ from the logarithmic pole ladder in (1).

## 8. Reproducible numerical findings and the exact product

The retained computation uses 384-bit directed arithmetic, 220 exact rational
bisections per root, and independent 100-decimal checks of seven selected
roots. It includes every \(n\le1024\), exact formal coefficients through
\(J=4\), and the explicit remainder (26). The result is
\[
\boxed{\mathcal P\in
[1.40046736715264\ \pm\ 4.67\times10^{-15}].}
\tag{31}
\]
The analytic logarithmic remainder is below
\(1.148215\times10^{-15}\). Directed evaluation gives
\[
Z_R(2)\in[0.037438779916147694154\ \pm\ 3.38\times10^{-22}],
\]
and
\[
Z_R(-1/2+3i/4)\in
[-0.71222804630\pm4.75\times10^{-12}]
+i[0.65237835869\pm1.20\times10^{-12}].
\]
The independent \(N=512\) and \(N=1024\) product enclosures overlap.

The complete parameter-modulus determinant has the striking enclosure
\[
\boxed{e^{-2\sin d}\mathcal P^4
\in[1.0000000000000\ \pm\ 4.60\times10^{-15}].}
\tag{32}
\]
The experiment led to the now-proved exact identity:
\[
\boxed{\prod_{n\ge1}\frac{R_n}{2\pi n}=e^{\sin d/2},
\quad\text{equivalently}\quad e^{-Z_{|L|}'(0)}=1.}
\tag{33}
\]
The companion trace proof establishes (33) exactly; the directed computation
checks the normalization through a separate real-radius calculation. The
finite Dottie pair and the entire infinite quartet family therefore have an
exact shared product invariant. This is the link between the radial zeta
and the Joukowski entire determinant: their regularized traces evaluate the
same quantity in different coordinates.

Reproduction:

```powershell
$env:PYTHONPATH=Join-Path (Get-Location) 'work/deps'
& 'work/exploration-lab-runtime/Scripts/python.exe' `
  'outputs/Greater-Works-Quartet-Spectrum/computations/derive_radial_coefficients.py'
& 'work/exploration-lab-runtime/Scripts/python.exe' `
  'outputs/Greater-Works-Quartet-Spectrum/computations/verify_radial_zeta.py'
```

The exact coefficient computation took about 1.8 seconds and the numerical
run about 1.7 seconds on the current CPU. Their JSON records retain root
brackets for selected indices, a SHA256 of the complete rational-bracket
stream, formal polynomials, explicit analytic constants, both cutoff
comparisons and every quoted enclosure. All work is headless CPU research.
