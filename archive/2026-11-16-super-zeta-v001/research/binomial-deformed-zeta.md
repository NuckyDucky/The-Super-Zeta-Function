# A central-binomial deformation of the quartet super-zeta

16 November 2026. This note turns the normalized levels
\(C_n=R_nB_n^2/2\) into a two-variable Dirichlet family, identifies its
meromorphic structure, and evaluates a new spectral determinant exactly.

Retain the positive real logarithm of every \(C_n\), and put
\[
\boxed{\mathfrak Z(s,w)=\sum_{n\ge1}n^{-s}C_n^w,
\qquad\Re s>1,\quad w\in\mathbb C.}
\tag{1}
\]
The index variable \(s\) grades the quartet levels, while \(w\) varies
the strength of the exact central-binomial normalization. The bounded
positive sequence \(C_n\to1\) makes (1) normally convergent on every
compact subset of this domain, jointly holomorphic in \(s,w\).

The exact input from the companion product theorem is
\[
K=\lim_{N\to\infty}N^{1/4}\prod_{n=1}^NC_n
=\frac{e^{\sin d/2}}{G(3/2)^2}.
\tag{2}
\]

## 1. All-order continuation

Write \(L_n=\log(2\pi n)\). The radial and Stirling expansions combine
as
\[
\log C_n\sim\sum_{m\ge1}u_m(L_n)n^{-m},
\]
\[
\boxed{u_{2j}(L)=\frac{\chi_j(L)}{(2\pi)^{2j}},\qquad
u_{2j-1}=d_{2j-1}.}
\tag{3}
\]
Here \(\chi_j\) are the exact radial logarithmic polynomials, of degree
\(2j\), and
\(d_{2j-1}=-4(1-2^{-2j})B_{2j}/[(2j)(2j-1)]\).
Their remainders are controlled in the companion normalization note.
For every fixed truncation order these formulas are uniform, including
the estimates needed after differentiating in \(w\) on compact sets.

Define the rational-polynomial coefficient family
\[
\boxed{E_m(w,L)=[x^m]\exp\!\left(w\sum_{k\ge1}u_k(L)x^k\right),
\qquad E_0=1.}
\tag{4}
\]
A closed recurrence is
\[
\boxed{E_m(w,L)=\frac wm\sum_{k=1}^m k\,u_k(L)E_{m-k}(w,L).}
\tag{5}
\]
In particular
\[
E_1=-w/4,
\]
\[
E_2=\frac{w(2L^2-2L-1)}{4\pi^2}+\frac{w^2}{32},
\]
\[
E_3=\frac w{96}-\frac{w^2(2L^2-2L-1)}{16\pi^2}
-\frac{w^3}{384}.
\tag{6}
\]
For \(c=\log(2\pi)\), asymptotic subtraction yields
\[
\boxed{\mathfrak Z(s,w)=
\sum_{m=0}^M E_m(w,c-\partial_s)\zeta(s+m)
+\mathcal R_M(s,w),}
\tag{7}
\]
where the derivatives act on the zeta function and
\(\mathcal R_M\) is jointly holomorphic for \(\Re s>-M\),
\(w\in\mathbb C\). To prove this, subtract the corresponding terms
from each summand of (1). The remainder is
\(O_K((1+\log n)^{M+1}n^{-\Re s-M-1})\) on compact parameter sets,
so its series converges normally in that half-plane. Increasing \(M\)
continues (1) through the entire \(s\)-plane.

**Proposition.** The family \(\mathfrak Z\) is jointly meromorphic on
\(\mathbb C^2\), entire in \(w\), with possible polar hyperplanes
\(s=1-m\), \(m\ge0\). Their order is at most
\(2\lfloor m/2\rfloor+1\). At \(s=1\) the residue is one; at
\(s=0\),
\[
\boxed{\operatorname{Res}_{s=0}\mathfrak Z(s,w)=-w/4.}
\tag{8}
\]
For \(j\ge1\), the highest Laurent coefficients at the two subsequent
types of hyperplane are
\[
\boxed{
[ (s-(1-2j))^{-2j-1}]\mathfrak Z(s,w)
=\frac{(2j)!}{\pi^{2j}}\binom{w/2}{j},}
\tag{9}
\]
\[
\boxed{
[ (s+2j)^{-2j-1}]\mathfrak Z(s,w)
=-\frac{w(2j)!}{4\pi^{2j}}\binom{w/2}{j}.}
\tag{10}
\]
Whenever the displayed coefficient is nonzero, that pole has exactly the
stated order. The recurrence (5) determines every lower coefficient and
the reduced orders at exceptional \(w\).

**Proof of the highest coefficients.** At radial order \(n^{-2j}\), the
highest logarithmic degree of \((R_n/(2\pi n))^w\) is the coefficient
of the formal leading expression
\((1+L_n^2/(\pi^2n^2))^{w/2}\). Thus
\[
[L^{2j}]E_{2j}(w,L)=\pi^{-2j}\binom{w/2}{j}.
\]
The radial expansion has only even inverse powers. At odd order
\(2j+1\), the only contribution of this same logarithmic degree is
its product with the leading central-binomial term \(-w/(4n)\),
giving the coefficient in (10). Finally
\(\sum n^{-q}(\log n)^k=(-\partial_q)^k\zeta(q)\) has principal
part \(k!/(q-1)^{k+1}\). This proves (9)–(10). ∎

## 2. The Barnes constant is a finite-part invariant of the deformation

Let
\[
h_n=\log C_n+\frac1{4n}.
\]
The series \(\sum|h_n|\) converges, since
\(h_n=O((\log n)^2/n^2)\). Taking the logarithm in (2) gives
\[
\boxed{\sum_{n\ge1}h_n=\log K+\gamma/4.}
\tag{11}
\]
For \(\Re s>0\), then by continuation to a neighborhood of zero,
\[
\left.\partial_w\mathfrak Z(s,w)\right|_{w=0}
=-\frac14\zeta(s+1)+\sum_{n\ge1}n^{-s}h_n.
\]
Its constant Laurent coefficient at zero is therefore
\[
\boxed{\operatorname{FP}_{s=0}
\left.\partial_w\mathfrak Z(s,w)\right|_{w=0}
=\log K=\frac{\sin d}{2}-2\log G(3/2).}
\tag{12}
\]
This identifies the global normalized product as a concrete finite-part
trace of the two-variable super-zeta. The quartet correction and the
balanced-sign correction enter the same analytic invariant.

## 3. A normalized linear spectrum has an exact zeta determinant

The positive levels
\[
\boxed{\Lambda_n=nC_n=n\frac{R_nB_n^2}{2}}
\tag{13}
\]
satisfy \(\Lambda_n=n-1/4+o(1)\). They define a positive self-adjoint
diagonal operator on \(\ell^2\) with compact resolvent. Its spectral zeta
is the diagonal restriction
\[
\boxed{Z_\Lambda(s)=\mathfrak Z(s,-s)=\sum_{n\ge1}\Lambda_n^{-s}.}
\tag{14}
\]

**Theorem.** This spectral zeta continues meromorphically to the whole
plane. It has a simple pole of residue one at \(s=1\); it is regular
at zero, where
\[
\boxed{Z_\Lambda(0)=-\tfrac14,\qquad
Z_\Lambda'(0)=-\tfrac12\log(2\pi)-\log K.}
\tag{15}
\]
Its zeta-regularized determinant is exactly
\[
\boxed{\det{}_\zeta\Lambda
=\sqrt{2\pi}\,K
=\frac{\sqrt{2\pi}\,e^{\sin d/2}}{G(3/2)^2}.}
\tag{16}
\]
Every negative integer is a pole. For each \(j\ge1\), the poles at
\(-(2j-1)\) and \(-2j\) both have order \(2j+1\). Their respective
highest Laurent coefficients are
\[
\boxed{\frac{((2j)!)^2}{(2\pi)^{2j}(j!)^2},
\qquad -\frac{j(2j)!}{2\pi^{2j}}.}
\tag{17}
\]

**Proof near zero.** Set \(H(s)=\sum n^{-s}h_n\), holomorphic for
\(\Re s>-1\). Taylor's theorem and
\(\log C_n=O(1/n)\) show that
\[
Q(s)=\sum n^{-s}
[e^{-s\log C_n}-1+s\log C_n]
\]
is holomorphic near zero and \(Q(s)=O(s^2)\). Therefore
\[
Z_\Lambda(s)=\zeta(s)+\frac s4\zeta(s+1)-sH(s)+Q(s).
\]
Using \(H(0)=\log K+\gamma/4\),
\(\zeta(0)=-1/2\), \(\zeta'(0)=-\log(2\pi)/2\), and the Laurent
constant \(\gamma\) of \(\zeta(s+1)\), one obtains (15)–(16).
The apparent pole from (8) becomes the finite contribution \(+1/4\)
on \(w=-s\).

For the remaining poles, substitute \(w=-s\) into (9)–(10). At
\(s=1-2j\), \(w=2j-1\), and
\(\binom{j-1/2}{j}=(2j)!/[4^j(j!)^2]\). At \(s=-2j\),
\(w=2j\) and \(\binom jj=1\). Both highest coefficients are nonzero,
giving (17) and the complete pole list. ∎

The classical Riemann-zeta values and pole normalization used here are
[NIST DLMF §25.2](https://dlmf.nist.gov/25.2) and
[§25.6](https://dlmf.nist.gov/25.6). All family-specific continuation,
finite-part and determinant calculations are derived above.

## 4. Computation and interpretation

The exact script `verify_binomial_normalization.py` constructs (3)–(5)
through \(m=8\), verifies the highest logarithmic coefficients symbolically,
and checks their nonvanishing on the spectral diagonal. Directed evaluation
of the closed determinant gives
\[
\boxed{\det{}_\zeta\Lambda
=3.0706239160250272388866383032834685303194664518609132\ldots.}
\]
The companion finite-cutoff certificates independently recover the
constant \(K\) from 1,024 actual quartet radii and exact balanced-sign
probabilities. Their controlled errors and precision records are retained
in `computations/binomial-normalization-results.json`.

The three exact levels now have explicit relations: \(C_n\to1\), the
product requires \(N^{1/4}\), and its normalization constant is the
finite-part trace (12). Keeping the level index produces the linear
spectrum \(\Lambda_n\), whose zeta value and determinant remember that
same quarter-shift and Barnes–Dottie constant.
