# The radial product is exactly the exponential of half the Dottie sine

16 November 2026. The directed radial-product experiment led to the identity
\[
\boxed{\prod_{n=1}^{\infty}\frac{R_n}{2\pi n}
=\exp\!\left(\frac{\sin d}{2}\right),\qquad d=\cos d.}
\tag{1}
\]
This note proves it by computing one analytically continued trace in two
coordinates. The entire reciprocal quotient supplies its closed value;
the complex zero asymptotics express it as the convergent radial product.

## 1. The exact trace and its positive-half-plane spectrum

Write \(s_d=\sin d\), \(x_0=2s_d\), and retain the reciprocal quotient
\[
\mathcal J(x)=x\cosh\!\left(\frac{\sqrt{x^2-4}}2\right)
+\sqrt{x^2-4}\sinh\!\left(\frac{\sqrt{x^2-4}}2\right).
\]
Its zeros are \(x_0\) and \(x_n,\bar x_n\), where
\[
x_n=-2h_n+2iq_n,\qquad
h_n=\log R_n=t_n\coth t_n,\qquad
q_n=\sqrt{\sinh^2t_n-t_n^2}.
\]
Put
\[
a_n=-x_n=2h_n-2iq_n,\qquad \Re a_n>0,
\]
and use principal complex powers to define
\[
Z_a(z)=\sum_{n=1}^{\infty}
\left(a_n^{-z}+\bar a_n^{-z}\right),\qquad \Re z>1.
\tag{2}
\]
All arguments of \(a_n\) belong to \((-\pi/2,0)\), fixing this branch.

Remove the unique positive zero of \(\mathcal J\):
\[
G(t)=\frac{\mathcal J(t)}{\mathcal J(0)(1-t/x_0)},\qquad t\ge0.
\tag{3}
\]
The quotient has its removable value at \(t=x_0\). It is strictly positive:
\(G(0)=1\), it is real and has no real zero, and continuity preserves its
sign. Define
\[
g_1=G'(0)=-\frac{\cot1}{2}+\frac1{x_0}.
\]
The canonical product from the quotient theorem gives
\[
\log G(t)-g_1t
=\sum_{n\ge1}\left[
\log(1+t/a_n)-t/a_n+
\log(1+t/\bar a_n)-t/\bar a_n\right].
\tag{4}
\]
The logarithms are the branches continued from \(t=0\), equivalently the
principal logarithms of \(1+t/a_n\).

For \(1<\Re z<2\), integrating each term gives
\[
\int_0^\infty t^{-z-1}
\left[\log(1+t/a)-t/a\right]dt
=\frac{\pi a^{-z}}{z\sin\pi z},\qquad \Re a>0.
\]
Integration by parts reduces this to the beta integral. Absolute
interchange follows from the uniform right-half-plane estimate
\(|\log(1+w)-w|\le C\min(|w|^2,|w|+1+\log(1+|w|))\),
valid for \(\Re w\ge0\), and \(\sum|a_n|^{-\Re z}<\infty\).
Consequently,
\[
\boxed{Z_a(z)=\frac{z\sin\pi z}{\pi}
\int_0^\infty t^{-z-1}[\log G(t)-g_1t]dt,
\quad 1<\Re z<2.}
\tag{5}
\]

As \(t\to+\infty\), direct expansion of the exact determinant gives
\[
\log\mathcal J(t)=\frac t2+\log t-\frac1t+O(t^{-2}),
\]
and hence
\[
\boxed{\log G(t)=\frac t2+C+\frac{x_0-1}{t}+O(t^{-2}),
\quad C=\log\frac{x_0}{2\sin1}.}
\tag{6}
\]
The exponentially small second exponential in \(\mathcal J(t)\) preserves
this expansion. Subtracting these three large-t terms in (5) continues it
meromorphically through \(z=-1\). The only contribution at that point is
the coefficient of \(t^{-1}\):
\[
\boxed{Z_a(-1)=x_0-1.}
\tag{7}
\]
Indeed that Mellin term is \((x_0-1)/(z+1)\), while
\(z\sin(\pi z)/\pi=(z+1)+O((z+1)^2)\).
This is the elementary endpoint-subtraction mechanism described generally
in [NIST DLMF §2.5](https://dlmf.nist.gov/2.5).

## 2. The same trace isolates the convergent radial product

Let
\[
A_n=2\pi n,\qquad \ell_n=\log A_n,\qquad
Z(z)=(2\pi)^{-z}\zeta(z).
\]
The proved radial asymptotics give
\[
h_n=\ell_n+O(\ell_n^2/A_n^2),
\]
\[
2q_n=A_n-\frac{4\ell_n+2}{A_n}
+O(\ell_n^4/A_n^3),
\]
and therefore
\[
a_n=-iA_n+2\ell_n+i\frac{4\ell_n+2}{A_n}
+O(\ell_n^2/A_n^2).
\tag{8}
\]
For the second line, write \(r=e^{t_n}\). Then
\(2q_n=r-(2t_n^2+1)/r+O(t_n^4/r^3)\), and substitute
\(r=A_n+(2\ell_n^2-4\ell_n-1)/A_n+O(\ell_n^4/A_n^3)\).

Binomial expansion of the principal powers in (8), paired with their
conjugates, gives the explicit meromorphic model
\[
\begin{aligned}
M(z)={}&2\cos\frac{\pi z}{2}\,Z(z)
-4z\sin\frac{\pi z}{2}\,Z'(z+1)\\
&+2z\cos\frac{\pi z}{2}
\left[2Z(z+2)-4Z'(z+2)-2(z+1)Z''(z+2)\right].
\end{aligned}
\tag{9}
\]
More precisely, subtract the corresponding summand of (9) from
\(a_n^{-z}+\bar a_n^{-z}\). Uniformly on each compact subset of
\(\Re z>-2\), the remainder is
\(O_K(\ell_n^3 A_n^{-\Re z-3})\). The remainder series thus defines a
holomorphic function on that half-plane, and agrees with \(Z_a-M\) on
\(\Re z>1\).

At \(z=-1\), the model summand equals \(4\ell_n\), while the exact
summand equals \(4h_n\). Hence
\[
Z_a(-1)-M(-1)
=4\sum_{n\ge1}(h_n-\ell_n)
=4\log\prod_{n\ge1}\frac{R_n}{2\pi n}.
\tag{10}
\]
This is an ordinary absolutely convergent sum, since
\(h_n-\ell_n=O(\ell_n^2/A_n^2)\).

The value of M has a useful exact cancellation. The classical zeta values
\(\zeta(0)=-1/2\) and \(\zeta'(0)=-\log(2\pi)/2\), recorded in
[DLMF §25.6](https://dlmf.nist.gov/25.6) and
[DLMF 25.6.11](https://dlmf.nist.gov/25.6.E11), imply
\(Z'(0)=0\), so the first two terms of (9) vanish at \(z=-1\).
Set \(\delta=z+1\). Since
\[
Z(1+\delta)=\frac{r}{\delta}+b_0+b_1\delta+\cdots,
\qquad r=\frac1{2\pi},
\]
the bracket in (9) is
\[
2Z(1+\delta)-4Z'(1+\delta)-2\delta Z''(1+\delta)
=\frac{2r}{\delta}+O(1).
\]
Its apparent double poles cancel exactly. The remaining prefactor is
\[
2z\cos(\pi z/2)=-\pi\delta+O(\delta^2),
\]
giving
\[
\boxed{M(-1)=-2\pi r=-1.}
\tag{11}
\]
Combining (7), (10), and (11) yields
\[
x_0-1=-1+4\log\prod_{n\ge1}\frac{R_n}{2\pi n}.
\]
Since \(x_0=2\sin d\), this proves (1). ∎

## 3. The full parameter-modulus determinant

Include both Dottie parameters, with modulus \(e^{-\sin d}\), and all four
members of each nonunit quartet. The resulting modulus Dirichlet function is
\[
Z_{\rm mod}(z)=2e^{z\sin d}+4\sum_{n\ge1}R_n^{-z}.
\]
Near zero, the radial difference from Z is normally convergent, and
\[
\left.\frac d{dz}\left[\sum R_n^{-z}-Z(z)\right]\right|_{z=0}
=-\log\prod\frac{R_n}{2\pi n}=-\frac{\sin d}{2}.
\]
Because \(Z'(0)=0\), one obtains the exact cancellation
\[
\boxed{Z_{\rm mod}'(0)=0,\qquad
\det{}_{\zeta}(|L|\text{ spectrum})
:=\exp[-Z_{\rm mod}'(0)]=1.}
\tag{12}
\]
The finite Dottie contribution and the infinite quartet contribution are
linked by the exact product (1).

The argument uses two independently useful constructions: a determinant
with zeros in a fixed half-plane, and an asymptotic zeta model whose
remainder converges normally at the desired trace value. The universal
constant \(-1\) in (11) records the phase contribution in that model;
the remaining finite trace is the radial product.

## Reproduction

`computations/verify_product_trace_identity.py` checks the exact large-t
coefficient, generic Laurent cancellation, and binomial model algebra using
SymPy; it checks numerical model limits at 220 decimal digits. A separate
1024-bit directed Dottie isolation verifies that the exact-value ball for
\(\exp(\sin d/2)\) is contained in the retained 1024-root radial product
enclosure. The record, including the checksum of that independent product
computation, is `computations/product-trace-identity-results.json`.
