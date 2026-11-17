# The residue transform is an elliptic period and a random-chord moment function

16 November 2026. This note takes the exact central-binomial residues of the
shifted superzeta and develops their positive moment, geometric and modular
representations. Throughout this note K(m) uses the **parameter** convention
\[
K(m)=\int_0^{\pi/2}(1-m\sin^2\theta)^{-1/2}d\theta.
\]
Thus the NIST modulus k corresponds to m=k².

## 1. From pole residues to an elliptic differential equation

Let B_n=binom(2n,n)/4^n. The shifted superzeta proves that these are its
normalized pole residues. Their Hadamard-square generating function is
\[
\boxed{\mathcal M(z)=\sum_{n\ge0}B_n^2z^n
={}_2F_1(1/2,1/2;1;z)=\frac2\pi K(z),\quad |z|<1.}
\tag{1}
\]
The equality follows directly from B_n=(1/2)_n/n! and the hypergeometric
series; the elliptic representation is the classical identity
[DLMF 15.9.24](https://dlmf.nist.gov/15.9.E24), translated to the parameter
convention. Its ODE is
\[
\boxed{z(1-z)\mathcal M''+(1-2z)\mathcal M'-\tfrac14\mathcal M=0,}
\quad \mathcal M(0)=1,\quad\mathcal M'(0)=1/4.
\tag{2}
\]
The coefficient recurrence B_(n+1)/B_n=(2n+1)/(2n+2) proves (2) directly.

The same function is the normalized period
\[
\mathcal M(z)=\frac1\pi\int_0^1
\frac{dx}{\sqrt{x(1-x)(1-zx)}}
\tag{3}
\]
of the Legendre elliptic family Y²=x(1-x)(1-zx), away from z=0,1 and
the chosen period cuts. This elliptic curve is the period family of the
residue transform. The earlier fixed six-integer Hasse curve keeps its own
coefficients and arithmetic descent in the existing Greater Works archive.

## 2. A precise circle-chord model

Choose two endpoints independently and uniformly on a unit circle, and let
ell be their chord length. Repeated endpoint/chord configurations have
probability zero under this continuous distribution. The squared normalized
length
\[
X=\ell^2/4=\sin^2((\Theta_1-\Theta_2)/2)
\]
has the arcsine density
\[
f_X(x)=\frac1{\pi\sqrt{x(1-x)}},\qquad0<x<1.
\]
Changing variables from the uniform angle proves the density. Its moments are
the beta integral
\[
\boxed{\mathbb E[X^n]=\frac{\Gamma(n+1/2)}{\sqrt\pi\,\Gamma(n+1)}=B_n.}
\tag{4}
\]

Take two independent chords and Z=X_1X_2. Then
\[
\boxed{\mathbb E[Z^n]=B_n^2,
\qquad\mathcal M(z)=\mathbb E\frac1{1-zZ}.}
\tag{5}
\]
The product-density calculation is explicit:
\[
\boxed{f_Z(x)=\frac{2K(1-x)}{\pi^2\sqrt x},\qquad0<x<1.}
\tag{6}
\]
Indeed the multiplicative convolution is
\[
\frac1{\pi^2\sqrt x}\int_x^1
\frac{dt}{\sqrt{t(1-t)(t-x)}}.
\]
Substitution t=x+(1-x)sin²(theta) evaluates this integral as 2K(1-x).
This is a positive probability measure, giving a literal Stieltjes moment
representation of the squared superzeta residues.

The circle picture also admits an exact coverage observable. Associate to
each chord its shorter boundary arc, and normalize arc measure to total one.
The minor-arc fraction A is uniform on [0,1/2], with mean1/4. Each fixed
boundary point is uncovered by one chord with probability3/4. Independent
chords therefore have
\[
\boxed{\mathbb E[\text{covered fraction after N chords}]
=1-(3/4)^N,}
\]
\[
\boxed{\mathbb E[\text{new fraction from chord N}]
=\tfrac14(3/4)^{N-1}.}
\tag{7}
\]
Fubini's theorem proves the first formula pointwise, and successive differences
give the second. Thus the chosen geometry retains overlap explicitly in its
coverage statistic, while its length moments give the B_n coefficients.

The exact radius/chord moment observable is
\[
\boxed{\frac{R_n}{2}\mathbb E[Z^n]=\frac{R_nB_n^2}{2}.}
\tag{8}
\]
Its limit, finite corrections and renormalized product are the Barnes/radial
theorem of this continuation.

## 3. Positive approximation bounds and AGM computation

Since 0<=Z<=1, all moments are positive and decreasing. For 0<=z<1,
\[
\sum_{n=0}^NB_n^2z^n\le\mathcal M(z)
\le\sum_{n=0}^NB_n^2z^n+
\frac{B_{N+1}^2z^{N+1}}{1-z}.
\tag{9}
\]
This follows by bounding each omitted moment by B_(N+1)².

Gauss's AGM gives a much faster computation near the logarithmic endpoint:
\[
\boxed{\mathcal M(z)=1/\operatorname{AGM}(1,\sqrt{1-z}).}
\tag{10}
\]
For a0=1,b0=sqrt(1-z), iterate
a_(j+1)=(a_j+b_j)/2, b_(j+1)=sqrt(a_j b_j). Positivity gives
\[
\boxed{1/a_j\le\mathcal M(z)\le1/b_j.}
\tag{11}
\]
The gap contracts quadratically. Outward-rounded arithmetic makes each pair
an explicit certificate. The identity and AGM framework are classical;
see [DLMF 19.8](https://dlmf.nist.gov/19.8). Here they evaluate the exact
residue/chord transform supplied by (1).

## 4. The modular pullback of the residue function

For Im(tau)>0, put q=exp(pi i tau) and
\[
\lambda(\tau)=\theta_2(0|\tau)^4/\theta_3(0|\tau)^4.
\]
On the branch continued from the positive imaginary tau-axis,
\[
\boxed{\mathcal M(\lambda(\tau))=\theta_3(0|\tau)^2.}
\tag{12}
\]
This is the standard elliptic/theta identity
[DLMF 20.9.1–2](https://dlmf.nist.gov/20.9), now applied to the superzeta's
squared residue transform. The Fourier coefficients of theta3² count integer
representations by two squares, so the same function has a modular/lattice
description. The branch label is part of the period continuation; the scalar
hypergeometric series initially uses |z|<1.

Thus the sequence B_n² is simultaneously a balanced-history return probability,
a pair-of-chords moment, an elliptic period coefficient, and a squared
normalized superzeta residue. Each equivalence has an explicit transformation
and measure in this note.
