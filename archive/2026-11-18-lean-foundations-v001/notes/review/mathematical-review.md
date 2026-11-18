# Independent proof review: reciprocal dynamics and Dottie coefficient fields

Review date: 15 November 2026. The review independently derives the normalization, coefficient reconstruction, field degrees, and arithmetic deductions from the equations. The companion `independent_checks.py` performs exact symbolic checks and writes `independent-checks.json`.

## 1. The normalization is an explicit affine conjugacy

Let
\[
g_L(z)=\exp(Le^{-Lz}),\qquad g_L(p)=p,\qquad g_L'(p)=1,
\qquad L\ne0.
\]
Set \(\alpha=Le^{-Lp}\). Direct differentiation gives
\[
g_L'(p)=-Lp\alpha=1.
\]
The exact translated germ is
\[
g_L(p+u)-p=p\left[\exp\{\alpha(e^{-Lu}-1)\}-1\right].
\]
Its quadratic coefficient is \(a_2=-L(1+\alpha)/2\). For \(\alpha\ne-1\), the affine coordinate \(x=a_2u\) gives
\[
a_2\bigl[g_L(p+x/a_2)-p\bigr]
=\frac{1+\alpha}{2\alpha}
\left[\exp\left\{\alpha\left(e^{2x/(1+\alpha)}-1\right)\right\}-1\right]
=F_\alpha(x).
\]
All signs and factors agree. The normalization domain is \(\alpha\in\mathbb C\setminus\{0,-1\}\); the phase \(\alpha\) is automatically nonzero for the stated dynamical input.

### Exact compatibility of actual multiplier-one points

The fixed-point and multiplier equations give \(p=e^\alpha\) and \(L=-e^{-\alpha}/\alpha\). Substitution in \(\alpha=Le^{-Lp}\) yields the exact compatibility equation
\[
\boxed{\alpha^2e^{\alpha-\alpha^{-1}}=-1.}
\]
Conversely, for any nonzero solution of this equation, the displayed \(p,L\) give \(Le^{-Lp}=\alpha\), \(g_L(p)=p\), and \(g_L'(p)=1\). The equation has left side 1 at both \(\alpha=1\) and \(\alpha=-1\), excluding both. Hence every actual multiplier-one point has \(a_2\ne0\).

Every such \(\alpha\) is transcendental. Algebraicity would make \(\alpha-\alpha^{-1}\) a nonzero algebraic number, while the compatibility equation would make its exponential \(-\alpha^{-2}\) algebraic, contrary to Lindemann–Weierstrass. Combined with Section 3, this proves transcendence of every higher normalized coefficient at every actual multiplier-one fixed point. The script checks the exact residual factorization, converse substitution, multiplier, and both excluded endpoint values.

## 2. Coefficients and complete phase recovery

Expanding the nested exponential independently by truncated rational polynomial convolution agrees with
\[
h_n(\alpha)=\frac{2^{n-1}T_n(\alpha)}{n!\alpha(1+\alpha)^{n-1}}
\]
through order 14. In particular,
\[
h_3=\frac{2(\alpha^2+3\alpha+1)}{3(1+\alpha)^2},\qquad
h_4=\frac{\alpha^3+6\alpha^2+7\alpha+1}{3(1+\alpha)^3}.
\]
With \(\rho=1-h_3\), \(\theta=\alpha+\alpha^{-1}\), and
\[
w=\frac{24h_4-22+42\rho}{6\rho-2},
\]
exact simplification gives
\[
\rho=\frac{\theta}{3(\theta+2)},\quad
\theta=\frac{6\rho}{1-3\rho},\quad
w=\frac{\alpha-1}{\alpha+1},\quad
\alpha=\frac{1+w}{1-w}.
\]
The denominator \(6\rho-2=-4\alpha/(1+\alpha)^2\) is nonzero on the full normalization domain. Consequently
\[
\mathbb Q(h_3)=\mathbb Q(\theta),\qquad
\mathbb Q(h_3,h_4)=\mathbb Q(\alpha).
\]
For transcendental \(\alpha\), the first inclusion has degree two, with involution \(\alpha\mapsto\alpha^{-1}\). The discriminant \(\theta^2-4\) has simple zeros and hence is a nonsquare in \(\mathbb Q(\theta)\).

There is an independent degree check on the two-coefficient recovery. For transcendental \(\alpha\), the rational map \(h_4\) has degree three: its numerator and denominator have degree three, and the numerator evaluates to \(-1\) at \(\alpha=-1\), so they are coprime. Thus \([\mathbb Q(\alpha):\mathbb Q(h_4)]=3\). The extension over the joint field \(\mathbb Q(h_3,h_4)\) has degree dividing both 2 and 3, hence degree one.

## 3. Every higher coefficient classifies algebraicity of the phase

For each \(n\ge3\), the rational function \(h_n(\alpha)\) is nonconstant. In \(T_n(\alpha)/\alpha\), the leading coefficient is 1 and the next coefficient is \(n(n-1)/2\); in \((1+\alpha)^{n-1}\), those coefficients are 1 and \(n-1\). Their unequal second coefficients give nonconstancy for every \(n\ge3\).

A nonconstant rational function over \(\mathbb Q\) has algebraic fibers over \(\overline{\mathbb Q}\): if \(R(\alpha)=b\) is algebraic, clearing the denominator gives a nonzero polynomial equation for \(\alpha\) over \(\overline{\mathbb Q}\). Therefore the all-order conclusion is
\[
\boxed{h_n(\alpha)\in\overline{\mathbb Q}
\iff \alpha\in\overline{\mathbb Q}\qquad(n\ge3).}
\]
The proof is uniform in \(n\). Finite composition checks are recorded separately by their explicit order.

## 4. Dottie arithmetic and the second field diamond

Let \(d\in(0,1)\) satisfy \(d=\cos d\), put \(s=\sin d\), and \(\alpha=s+id\). Lindemann–Weierstrass makes \(d\) transcendental: algebraic nonzero \(d\) would produce the forbidden algebraic-coefficient linear relation \(e^{id}+e^{-id}-2d=0\) among exponentials of the distinct algebraic exponents \(id,-id,0\). The identity \(d^2+s^2=1\) then makes \(s\) transcendental. Algebraicity of \(\alpha\) would make its imaginary part \(d\) algebraic, so \(\alpha\) is transcendental too.

Because \(\alpha+\alpha^{-1}=2s\),
\[
\mathbb Q(h_3)=\mathbb Q(s),\qquad
\mathbb Q(h_3,h_4)=\mathbb Q(\alpha).
\]
The polynomials \(X^2-(1-s^2)\) and \(X^2-2sX+1\) have discriminants \(4(1-s^2)\) and \(4(s^2-1)\). Their simple roots prove that both extensions over \(\mathbb Q(s)\) are quadratic. The field \(\mathbb Q(d,s)\) is real, while \(\mathbb Q(\alpha)\) contains the nonreal \(\alpha\). Distinct quadratic extensions have intersection \(\mathbb Q(s)\). Their compositum is
\[
\mathbb Q(d,s,\alpha)=\mathbb Q(i,\alpha),
\]
with degree four and Galois group \(C_2\times C_2\).

## 5. Functional Ax applications

For \(\tau_0=z\), \(\tau_{j+1}=e^{c_j\tau_j}\), all \(c_j\ne0\), inductive algebraic independence implies that \(c_0\tau_0,\ldots,c_{n-1}\tau_{n-1}\) are rationally independent modulo the common derivative-constant field \(\mathbb C\). Their derivative matrix has rank one because \((c_0z)'=c_0\ne0\). Ax yields transcendence degree \(n+1\), equal to the number of tower generators. Taking alternating constants \(-L,L\) produces the finite reciprocal orbit families.

For two variables, with \(E=e^{-Lz}\) and exponents \(-Lz,LE\), the Jacobian determinant is \(LE\). The two exponentials are \(E,G\), and the exponentials-plus-exponents field recovers \(L,z\) rationally. Its transcendence degree is four. The hypotheses, field equalities, and constants are explicit in both applications.

The same tower induction permits affine outputs:
\[
\tau_{j+1}=A_j\exp(c_j\tau_j)+B_j,
\qquad A_jc_j\ne0.
\]
Indeed \(\exp(c_j\tau_j)=(\tau_{j+1}-B_j)/A_j\), so the generated field remains exactly the tower field. Since
\[
F_\alpha(x)=A\exp(\alpha\exp(\beta x))+B,\quad
A=\frac{1+\alpha}{2\alpha}e^{-\alpha},\quad
B=-\frac{1+\alpha}{2\alpha},\quad
\beta=\frac2{1+\alpha},
\]
every finite normalized-germ orbit-function family is algebraically independent for every \(\alpha\ne0,-1\). This strengthened corollary uses two successive affine-exponential stages per iterate.

The independent family has a removable extension at \(\alpha=0\):
\[
F_0(x)=\frac{e^{2x}-1}{2},\qquad h_n(0)=\frac{2^{n-1}}{n!}.
\]
For compact \(x\)-sets, the inner expression \(e^{2x/(1+\alpha)}-1\) is jointly analytic near \(\alpha=0\); the outer exponential's bracket is \(\alpha(e^{2x}-1)+O(\alpha^2)\), uniformly there. This proves the locally uniform limit. The one-stage affine-exponential tower theorem applies to \(F_0\), extending the orbit-function conclusion to every \(\alpha\ne-1\). The inverse-phase formulas retain their stated domain \(\alpha\ne0,-1\). The script checks the symbolic parameter limit and every coefficient limit through order 14.

## 6. Conditional arithmetic with an algebraic multiplier

For fixed phases \(P=e^U\), \(M=e^V\), with \(U=LM\), \(V=-LP\), and \(UV=\mu\in\overline{\mathbb Q}^{\times}\), both \(U,V\) are transcendental and rationally independent. If both were algebraic, \(e^{U-V}=-V/U\) and Lindemann–Weierstrass force \(U=V\), while compatibility forces \(U=-V\), contradicting \(UV\ne0\). Rational dependence would make \(U^2\) algebraic and return the same contradiction.

Under the Schanuel inequality for this exact pair \(U,V\), the field \(\mathbb Q(U,V,P,M)\) has transcendence degree at least two. Since \(U^2=-\mu M/P\) and \(V=\mu/U\), this gives algebraic independence of \(P,M\); the rational identities \(M=U/L\), \(P=-\mu/(LU)\) give independence of \(U,L\). At Dottie, \(U=\alpha\), \(L=ie^{-s}\), and \(d=(\alpha-\alpha^{-1})/(2i)\); finite algebraic extensions transfer this conclusion to \(d,e^{-s}\).

## Check record

The independent script passed on Python 3.12.11 / SymPy 1.14.0. It checks the exact affine conjugacy, two-stage affine decomposition, parameter-rank Jacobian, parabolic compatibility and converse, rational coefficient recovery and denominators, reduced map degrees two and three, reciprocal invariance, quadratic discriminants, the differential equation, 14 composition coefficients and zero-parameter coefficient limits, and Touchard derivatives through order 8. Its all-order and arbitrary-depth claims are supported by the proofs above.

## Final manuscript review: whole parabolic locus and the unit circle

The frozen manuscript's Theorem 4.1, Corollary 4.5, and Proposition 5.1 pass analytical review. Theorem 4.1 gives a bijection between actual multiplier-one parameter/fixed-point pairs and the nonzero solutions of the compatibility equation; the inverse explicitly recovers the original phase. The phase's transcendence and exclusion of both 1 and -1 make the quadratic coefficient nonzero throughout this actual locus.

For the reciprocal involution, the compatibility expression \(\alpha^2e^{\alpha-\alpha^{-1}}\) is inverted by \(\alpha\mapsto\alpha^{-1}\), preserving its value -1. The lift ratio is exactly that same expression, giving \(L\mapsto-L\) and interchanging the two fixed phases. Direct subtraction of the reduced quartic coefficient gives
\[
h_4(\alpha)-h_4(\alpha^{-1})
=\frac{\alpha(1-\alpha)}{3(1+\alpha)^3},
\]
which is nonzero at every actual parabolic phase. The cubic coefficient remains reciprocal-invariant.

For the complete unit-modulus classification, write \(\alpha=e^{i\theta}\) with \(-\pi<\theta<\pi\), using the already proved exclusion of -1. Compatibility becomes
\[
\theta+\sin\theta=(k+\tfrac12)\pi.
\]
The left side is odd, strictly increasing, and has range \((-\pi,\pi)\), because its derivative is \(1+\cos\theta>0\) on this open interval. Only the target values \(\pm\pi/2\) occur, each once. The positive solution lies in \((0,\pi/2)\). With \(d=\pi/2-\theta\), it gives \(d=\sin\theta=\cos d\), and \(0<d<1\). Therefore the two phases are exactly \(\sin d\pm id\). Substitution into \(L=-e^{-\alpha}/\alpha\) gives \(L=\pm i e^{-\sin d}\), with the signs and corresponding fixed points matching Proposition 5.1. This establishes the full stated classification.

The root's separate `parabolic_locus_checks.py` records exact reciprocal, quartic-difference, and angle-derivative identities plus its own 100/200-digit Dottie checks. The analytical argument above supplies completeness of the unit-circle classification. Final review completed; these review files are frozen for packaging.
