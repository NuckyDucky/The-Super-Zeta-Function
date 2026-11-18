# Functional independence and coefficient fields in reciprocal exponential dynamics

**A theorem note developed from Nick's reciprocal-tetration and Dottie constructions**  
15 November 2026 · Version 1.0

## Abstract

For the reciprocal exponential map \(g_L(z)=\exp(Le^{-Lz})\), with any fixed nonzero complex parameter \(L\), we prove that every finite family \(z,g_L(z),\ldots,g_L^{\circ m}(z)\) is algebraically independent over \(\mathbb C\). The proof applies Ax's differential theorem to finite affine-exponential towers. A two-variable deformation has transcendence degree four, and an exact differential equation generates the Touchard derivative hierarchy. Every multiplier-one fixed point is simple parabolic and corresponds to a solution of \(\alpha^2e^{\alpha-\alpha^{-1}}=-1\); every such phase \(\alpha\) and all its higher normalized germ coefficients are transcendental. Reciprocal substitution preserves this locus and changes \(L\) to \(-L\). The cubic coefficient retains that reciprocal pair, while the quartic distinguishes its two members; their fields have respective indices two and three and jointly recover \(\alpha\) rationally. The Dottie phase and its conjugate are exactly the unit-modulus points of this parabolic locus, and their coefficient fields fit into an explicit biquadratic diamond. For the universal normalized family, orbit-function independence extends to every \(\alpha\ne-1\), including its removable value at zero. A final conditional corollary isolates the two-logarithm Schanuel instance governing the distinguished numerical lift. Complete proofs follow. These statements are presented as derived applications of established transcendence theorems and direct calculations for the specified dynamical family.

## 1. Setting and main statements

Write

\[
\mathcal R_L(P,M)=(e^{LM},e^{-LP}),\qquad
g_L(z)=e^{Le^{-Lz}}.
\tag{1.1}
\]

A fixed pair \((P,M)\) of \(\mathcal R_L\) supplies a fixed point \(P\) of \(g_L\). Complex exponentiation in this note uses the ordinary single-valued exponential. When we introduce logarithmic coordinates, the displayed dynamical equations select their values.

For a field \(k\), a family is **algebraically independent over \(k\)** if evaluating a nonzero polynomial with coefficients in \(k\) at that family always gives a nonzero element. For analytic functions, this is a statement about identities of functions on a connected domain, or equivalently their meromorphic germs. For numerical constants, the base field in our arithmetic statements is \(\mathbb Q\).

For the numerical arithmetic proofs, we use the Lindemann–Weierstrass theorem: exponentials of distinct algebraic numbers are linearly independent over the algebraic numbers [4]. In particular the exponential of a nonzero algebraic number is transcendental.

The principal conclusions are:

1. For every fixed \(L\ne0\), the functions \(z,g_L(z),\ldots,g_L^{\circ m}(z)\) are algebraically independent over \(\mathbb C\) for every finite \(m\).
2. The four functions \(L,z,e^{-Lz},e^{Le^{-Lz}}\), in two independent variables, are algebraically independent over \(\mathbb C\).
3. Every multiplier-one fixed point is simple parabolic. Its phase satisfies the exact compatibility equation \(\alpha^2e^{\alpha-\alpha^{-1}}=-1\), and every such phase and higher normalized coefficient is transcendental. The Dottie pair is its complete unit-modulus locus.
4. The normalized germ has an exact Touchard coefficient formula, with \(h_3,h_4\) recovering its phase rationally. Its finite orbit-function families are algebraically independent at every \(\alpha\ne-1\), using the removable extension at zero. Each higher coefficient detects whether the phase is algebraic or transcendental.
5. At the Dottie parameter,
   \[
   \mathbb Q(h_3)=\mathbb Q(\sin d),\qquad
   \mathbb Q(h_3,h_4)=\mathbb Q(\sin d+id).
   \]

The source identities from the two supplied preprints enter in Section 5, where they are also derived directly from (1.1).

## 2. Ax's theorem and finite exponential towers

We use the following differential form of Ax's theorem [1–3]. Let \(F\) be a field of characteristic zero with commuting derivations \(D_1,\ldots,D_r\), and let \(C\) be its common field of constants. Suppose \(x_j,y_j\in F\), with \(y_j\ne0\), satisfy

\[
D_a y_j=y_jD_a x_j.
\]

If \(x_1,\ldots,x_n\) are linearly independent over \(\mathbb Q\) modulo \(C\), then

\[
\operatorname{trdeg}_{C} C(x_1,\ldots,x_n,y_1,\ldots,y_n)
\ge n+\operatorname{rank}_{F}(D_a x_j).
\tag{2.1}
\]

Here independence modulo \(C\) means that a rational linear combination belonging to \(C\) has all coefficients zero. We apply (2.1) in fields of meromorphic functions or germs, using the coordinate partial derivatives. The common constants are \(\mathbb C\).

**Theorem 2.1 (finite affine-exponential towers).** Fix \(n\ge0\), constants \(A_j,c_j\in\mathbb C\setminus\{0\}\), and \(B_j\in\mathbb C\), for \(0\le j<n\). Define entire functions

\[
\tau_0(z)=z,\qquad
\tau_{j+1}(z)=A_j\exp(c_j\tau_j(z))+B_j.
\tag{2.2}
\]

Then \(\tau_0,\ldots,\tau_n\) are algebraically independent over \(\mathbb C\).

*Proof.* Induct on \(n\). For \(n=0\), the function \(z\) is transcendental over the constant field. Suppose \(\tau_0,\ldots,\tau_{n-1}\) are algebraically independent. Set

\[
x_j=c_{j-1}\tau_{j-1},\qquad
y_j=\frac{\tau_j-B_{j-1}}{A_{j-1}}=e^{x_j},
\qquad 1\le j\le n.
\]

A rational linear relation \(\sum_jq_jx_j\in\mathbb C\) would be a polynomial relation among \(\tau_0,\ldots,\tau_{n-1}\). Their algebraic independence and \(c_j\ne0\) give \(q_j=0\) for every \(j\). The derivative matrix has one row and rank one, because \(x_1'=c_0\ne0\). Equation (2.1) therefore gives

\[
\operatorname{trdeg}_{\mathbb C}
\mathbb C(x_1,\ldots,x_n,y_1,\ldots,y_n)\ge n+1.
\]

The displayed field is exactly \(\mathbb C(\tau_0,\ldots,\tau_n)\), with \(n+1\) generators. Its transcendence degree is \(n+1\), completing the induction. \(\square\)

**Corollary 2.2 (reciprocal orbit functions).** For every fixed \(L\in\mathbb C\setminus\{0\}\) and every \(m\ge0\),

\[
z,\quad g_L(z),\quad g_L^{\circ2}(z),\quad\ldots,\quad
g_L^{\circ m}(z)
\tag{2.3}
\]

are algebraically independent over \(\mathbb C\).

*Proof.* Use Theorem 2.1 with \(A_j=1\), \(B_j=0\), and \(c_0=-L,c_1=L,c_2=-L,c_3=L,\ldots\). Then \(\tau_{2j}=g_L^{\circ j}(z)\). The functions in (2.3) are a subfamily of an algebraically independent tower. \(\square\)

At \(L=0\), the map is the constant function \(1\); this is the excluded parameter. For fixed nonzero \(L\), the conclusion holds for germs at every finite starting point because an identity on a germ extends to an identity of entire functions.

The same conclusion is preserved by an invertible affine coordinate change. If \(A(z)=az+b\), \(a\ne0\), and \(f=A\circ g_L\circ A^{-1}\), then \(f^{\circ j}=A\circ g_L^{\circ j}\circ A^{-1}\). Substitution by \(A\) in the variable and in each coordinate is an invertible transformation of the corresponding polynomial relations over \(\mathbb C\).

## 3. A two-variable deformation and the differential hierarchy

**Theorem 3.1 (parameter rank).** In the two independent complex variables \(L,z\), the functions

\[
L,\qquad z,\qquad E=e^{-Lz},\qquad G=e^{LE}
\tag{3.1}
\]

are algebraically independent over \(\mathbb C\).

*Proof.* Choose \(x_1=-Lz\), \(x_2=LE\), so \(e^{x_1}=E\), \(e^{x_2}=G\). Their Jacobian is

\[
\frac{\partial(x_1,x_2)}{\partial(L,z)}=
\begin{pmatrix}
-z&-L\\
E(1-Lz)&-L^2E
\end{pmatrix},\qquad \det=LE.
\tag{3.2}
\]

This is a nonzero meromorphic function, hence the differential rank is two. It also shows that \(x_1,x_2\) are rationally linearly independent modulo constants. Ax gives transcendence degree at least four for \(\mathbb C(x_1,x_2,E,G)\). As elements of the meromorphic function field,

\[
L=x_2/E,\qquad z=-x_1/L.
\]

Thus this field equals \(\mathbb C(L,z,E,G)\), generated by four elements, and its transcendence degree is four. \(\square\)

The theorem concerns the two-variable family. Corollary 2.2 supplies the corresponding fixed-nonzero-parameter statement.

Define the Touchard polynomials by

\[
T_n(W)=\sum_{k=0}^n {n\brace k}W^k,
\qquad T_0=1,
\]

where \({n\brace k}\) are Stirling numbers of the second kind. Their recurrence is

\[
T_{n+1}(W)=W\bigl(T_n(W)+T_n'(W)\bigr).
\tag{3.3}
\]

**Proposition 3.2 (differential identities).** For fixed \(L\),

\[
GG''-(G')^2+LGG'=0,
\qquad
G^{(n)}(z)=(-L)^nT_n(Le^{-Lz})G(z)
\tag{3.4}
\]

for every \(n\ge0\), with derivatives taken in \(z\).

*Proof.* Write \(W=Le^{-Lz}\). Then \(W'=-LW\) and \(G=e^W\). Consequently \(G'/G=-LW\), and

\[
(G'/G)'=L^2W=-L(G'/G).
\]

Multiplying by \(G^2\) gives the differential equation. The derivative formula holds at \(n=0\). Differentiating its right side and using \(W'=-LW\) gives (3.3), proving the formula by induction. \(\square\)

## 4. Parabolic normalization and finite coefficient recovery

Let \(L\ne0\), let \(p=g_L(p)\), and put

\[
\alpha=Le^{-Lp}.
\]

The exponential makes \(p\ne0\), and \(\alpha\ne0\). Direct expansion gives the exact translated germ

\[
g_L(p+u)-p
=p\left[\exp\!\left(\alpha(e^{-Lu}-1)\right)-1\right].
\tag{4.1}
\]

Assume its multiplier is one. Since \(g_L'(p)=-Lp\alpha\), this is

\[
-Lp\alpha=1.
\tag{4.2}
\]

**Theorem 4.1 (the complete multiplier-one locus).** All parameter–fixed-point pairs \((L,p)\) with \(L\ne0\), \(g_L(p)=p\), and \(g_L'(p)=1\) are parametrized bijectively by the nonzero complex solutions of

\[
\boxed{\alpha^2\exp(\alpha-\alpha^{-1})=-1,}
\qquad
p=e^\alpha,\quad L=-\frac{e^{-\alpha}}\alpha.
\tag{4.2a}
\]

Every such \(\alpha\) is transcendental and differs from \(1,-1\). Every multiplier-one fixed point has a nonzero quadratic coefficient, and hence is simple parabolic. The reciprocal substitution \(\alpha\mapsto\alpha^{-1}\) preserves the locus and interchanges

\[
(L,P,M)\longmapsto(-L,M,P),\qquad
P=e^\alpha,\quad M=e^{\alpha^{-1}}.
\tag{4.2b}
\]

*Proof.* The fixed-point equation gives \(p=e^\alpha\), and (4.2) gives \(L=-e^{-\alpha}/\alpha\). Also \(-Lp=\alpha^{-1}\), so the defining identity \(\alpha=Le^{-Lp}\) gives \(\alpha=L e^{\alpha^{-1}}\). Substitution of \(L\) yields (4.2a).

Conversely, choose a nonzero solution of (4.2a), and define \(L,p\) by its formulas. Then \(-Lp=\alpha^{-1}\) and

\[
Le^{-Lp}=-\frac{e^{-\alpha+\alpha^{-1}}}\alpha=\alpha,
\]

using \(e^{-\alpha+\alpha^{-1}}=-\alpha^2\). Hence \(g_L(p)=e^\alpha=p\), and \(g_L'(p)=-Lp\alpha=1\). The construction recovers the original \(\alpha\), proving the bijection.

At \(\alpha=1\) or \(-1\), the left side of (4.2a) is one, so both values are excluded. If \(\alpha\) were algebraic, the exponent \(\alpha-\alpha^{-1}\) would be nonzero algebraic. Lindemann–Weierstrass would make its exponential transcendental, whereas (4.2a) gives the algebraic value \(-\alpha^{-2}\). Thus \(\alpha\) is transcendental.

Replacing \(\alpha\) by its reciprocal in the locus equation takes its left side to its multiplicative inverse, still \(-1\). The corresponding parameters satisfy

\[
\frac{L(\alpha^{-1})}{L(\alpha)}
=\alpha^2e^{\alpha-\alpha^{-1}}=-1.
\]

The two phase formulas are interchanged, proving (4.2b). Finally, (3.4) gives the quadratic coefficient

\[
\frac{g_L''(p)}2
=\frac{pL^2(\alpha^2+\alpha)}2
=-\frac{L(1+\alpha)}2,
\]

which is nonzero because \(L\ne0\) and \(\alpha\ne-1\). \(\square\)

The quadratic coefficient in (4.1) is

\[
a_2=-\frac{L(1+\alpha)}2.
\tag{4.3}
\]

This is nonzero at every actual multiplier-one fixed point, by Theorem 4.1. The affine coordinate \(x=a_2(z-p)\) gives

\[
F_\alpha(x)=a_2\left[g_L\left(p+\frac{x}{a_2}\right)-p\right]
=\frac{1+\alpha}{2\alpha}
\left[\exp\!\left(\alpha(e^{2x/(1+\alpha)}-1)\right)-1\right].
\tag{4.4}
\]

This is the exact normalization used throughout this note: the linear and quadratic coefficients are both one. The abstract value \(\alpha=-1\) is excluded from this formula; Theorem 4.1 shows that actual multiplier-one fixed points automatically avoid it.

Formula (4.4) also defines an entire function of \(x\) for every numerical \(\alpha\ne0,-1\), independently of its occurrence as a dynamical parameter.

**Proposition 4.2 (coefficients and recovery).** Write

\[
F_\alpha(x)=x+x^2+\sum_{n\ge3}h_n(\alpha)x^n.
\]

For \(\alpha\ne0,-1\),

\[
h_n(\alpha)=
\frac{2^{n-1}T_n(\alpha)}{n!\alpha(1+\alpha)^{n-1}}
\quad(n\ge1).
\tag{4.5}
\]

Put \(\rho=1-h_3\) and \(\theta=\alpha+\alpha^{-1}\). Then

\[
h_3=\frac{2(\alpha^2+3\alpha+1)}{3(\alpha+1)^2},\qquad
h_4=\frac{\alpha^3+6\alpha^2+7\alpha+1}{3(\alpha+1)^3},
\tag{4.6}
\]

\[
\rho=\frac{\theta}{3(\theta+2)},\qquad
\theta=\frac{6\rho}{1-3\rho}.
\tag{4.7}
\]

Moreover, the quantities

\[
w=\frac{24h_4-22+42\rho}{6\rho-2},\qquad
\alpha=\frac{1+w}{1-w}
\tag{4.8}
\]

give rational recovery of \(\alpha\). Consequently, for every numerical \(\alpha\ne0,-1\),

\[
\boxed{\mathbb Q(h_3)=\mathbb Q(\theta),\qquad
\mathbb Q(h_3,h_4)=\mathbb Q(\alpha).}
\tag{4.9}
\]

*Proof.* The exponential generating function

\[
\exp\!\left(\alpha(e^t-1)\right)
=\sum_{n\ge0}T_n(\alpha)\frac{t^n}{n!}
\]

follows either by expanding \(e^{\alpha e^t}\), or by the recurrence (3.3). Substituting \(t=2x/(1+\alpha)\) proves (4.5) and gives (4.6). Subtracting \(h_3\) from one yields

\[
\rho=\frac{\alpha^2+1}{3(\alpha+1)^2},
\]

which proves (4.7). Its denominators are nonzero because

\[
\theta+2=\frac{(\alpha+1)^2}{\alpha},
\qquad 1-3\rho=\frac{2\alpha}{(\alpha+1)^2}.
\]

Substitution of (4.6) into (4.8) gives

\[
6\rho-2=-\frac{4\alpha}{(\alpha+1)^2},
\qquad w=\frac{\alpha-1}{\alpha+1},
\qquad 1-w=\frac2{\alpha+1}.
\]

All are valid on the stated domain. Every coefficient in (4.6) is rational in \(\alpha\), and the inverse formulas give exactly the two field equalities. \(\square\)

For a transcendental \(\alpha\), the first field in (4.9) is the fixed field of the order-two substitution \(\alpha\mapsto\alpha^{-1}\). Indeed \(\alpha\) satisfies \(X^2-\theta X+1=0\), and the substitution defines a nontrivial automorphism of \(\mathbb Q(\alpha)\) fixing \(\theta\). The cubic coefficient therefore retains the reciprocal quotient, while the quartic coefficient recovers the phase.

There is a complementary degree description for transcendental \(\alpha\):

\[
[\mathbb Q(\alpha):\mathbb Q(h_3)]=2,\qquad
[\mathbb Q(\alpha):\mathbb Q(h_4)]=3.
\tag{4.9a}
\]

The two rational maps in (4.6) have degrees two and three. The numerator polynomials \(\alpha^2+3\alpha+1\) and \(\alpha^3+6\alpha^2+7\alpha+1\) both take the value \(-1\) at \(\alpha=-1\), so they are coprime to the respective denominator powers of \(\alpha+1\). For a reduced nonconstant rational function \(f/g\), the rational-function-field extension \(\mathbb Q(X)/\mathbb Q(f(X)/g(X))\) has degree \(\max(\deg f,\deg g)\). Indeed, in \(\mathbb Q[X,t]\), a factorization of \(f(X)-tg(X)\) must have a factor independent of \(t\); that factor divides both \(f\) and \(g\), so is a unit. The polynomial is primitive over \(\mathbb Q[t]\) because \(f/g\) is nonconstant. Gauss's lemma therefore gives irreducibility over \(\mathbb Q(t)\), proving the degree assertion and (4.9a). The relative degree over \(\mathbb Q(h_3,h_4)\) divides both two and three, giving another proof of the recovery field equality.

**Proposition 4.3 (each higher coefficient detects the arithmetic of the phase).** For every numerical \(\alpha\ne0,-1\) and every \(n\ge3\),

\[
h_n(\alpha)\in\overline{\mathbb Q}
\quad\Longleftrightarrow\quad
\alpha\in\overline{\mathbb Q}.
\tag{4.10}
\]

Moreover,

\[
[\mathbb Q(\alpha):\mathbb Q(h_n(\alpha))]\le n-1.
\tag{4.11}
\]

*Proof.* Formula (4.5) expresses \(h_n\) as a rational function over \(\mathbb Q\), with numerator and denominator degrees at most \(n-1\) after cancelling \(\alpha\). The numerator \(T_n(\alpha)/\alpha\) and denominator \((1+\alpha)^{n-1}\) are monic; their next coefficients are \(n(n-1)/2\) and \(n-1\), unequal for \(n\ge3\). Thus the rational function is nonconstant. An algebraic \(\alpha\) gives an algebraic value. Conversely, if the value were algebraic, clearing denominators would give a nonzero polynomial of degree at most \(n-1\), with algebraic coefficients, satisfied by \(\alpha\). This makes \(\alpha\) algebraic over \(\mathbb Q\). The same polynomial, now regarded over \(\mathbb Q(h_n(\alpha))\), gives the degree bound (4.11). \(\square\)

**Corollary 4.4 (functional independence for the whole normalized family).** For every fixed \(\alpha\in\mathbb C\setminus\{0,-1\}\) and every finite \(m\), the functions

\[
x,F_\alpha(x),\ldots,F_\alpha^{\circ m}(x)
\tag{4.12}
\]

are algebraically independent over \(\mathbb C\).

*Proof.* Write

\[
F_\alpha(x)=A\exp\!\left(\alpha e^{\beta x}\right)+B,
\quad
\beta=\frac2{1+\alpha},\quad
A=\frac{1+\alpha}{2\alpha}e^{-\alpha},\quad
B=-\frac{1+\alpha}{2\alpha}.
\]

Here \(A,\alpha,\beta\) are nonzero. Alternate the two stages \(t\mapsto e^{\beta t}\) and \(t\mapsto A e^{\alpha t}+B\) in Theorem 2.1. The even tower coordinates are precisely the iterates of \(F_\alpha\), so (4.12) follows. \(\square\)

**The removable parameter at zero.** For the independently defined normalized family, the apparent singularity at \(\alpha=0\) has the locally uniform limit

\[
F_0(x)=\frac{e^{2x}-1}{2},\qquad
h_n(0)=\frac{2^{n-1}}{n!}.
\tag{4.13}
\]

Expand the outer exponential of (4.4) in \(\alpha\); its bracket is \(\alpha(e^{2x}-1)+O(\alpha^2)\) uniformly on compact \(x\)-sets, which proves the limit. Theorem 2.1 applied to the single affine-exponential stage \(t\mapsto(e^{2t}-1)/2\) proves the orbit-function conclusion at this extended parameter too. Thus the functional conclusion extends to all \(\alpha\ne-1\). The reciprocal quotient and inverse formulas (4.7)–(4.8) retain their stated domain \(\alpha\ne0,-1\). Every actual multiplier-one fixed-point coordinate belongs to that domain by Theorem 4.1.

**Corollary 4.5 (coefficient arithmetic and reciprocal separation on the whole parabolic locus).** At every multiplier-one fixed point of every nonzero-parameter map \(g_L\), all higher normalized coefficients \(h_n\), \(n\ge3\), are transcendental. The coefficient fields satisfy

\[
[\mathbb Q(\alpha):\mathbb Q(h_3)]=2,\qquad
[\mathbb Q(\alpha):\mathbb Q(h_4)]=3,\qquad
\mathbb Q(h_3,h_4)=\mathbb Q(\alpha).
\tag{4.14}
\]

The cubic coefficient is unchanged by the reciprocal interchange (4.2b), while the quartic coefficient distinguishes its two phases:

\[
h_3(\alpha)=h_3(\alpha^{-1}),\qquad
h_4(\alpha)-h_4(\alpha^{-1})
=\frac{\alpha(1-\alpha)}{3(1+\alpha)^3}\ne0.
\tag{4.15}
\]

*Proof.* Theorem 4.1 makes \(\alpha\) transcendental. Propositions 4.2–4.3 and (4.9a) give the coefficient arithmetic and field statements. Reciprocal invariance of \(h_3\) follows from its expression through \(\theta\), and subtracting the two expressions for \(h_4\) in (4.6) gives (4.15). Theorem 4.1 excludes \(\alpha=0,1,-1\), so the difference is nonzero. \(\square\)

## 5. The Dottie point and the arithmetic of all higher coefficients

Let \(d\) be the unique solution in \((0,1)\) of \(d=\cos d\). Existence follows from the endpoint signs of \(\cos x-x\), and uniqueness from its strictly negative derivative on \((0,1)\). Set

\[
s=\sin d,\qquad y_*=e^{-s},\qquad
L_*=iy_*,\qquad \alpha=s+id.
\tag{5.1}
\]

Here \(s>0\), \(s^2+d^2=1\), and

\[
\alpha=ie^{-id},\qquad \alpha^{-1}=s-id=-ie^{id}.
\tag{5.2}
\]

The exact fixed pair is

\[
P=e^\alpha=e^s e^{id},\qquad
M=e^{\alpha^{-1}}=e^s e^{-id}.
\tag{5.3}
\]

Indeed \(L_*M=\alpha\) and \(-L_*P=\alpha^{-1}\), giving \(P=e^{L_*M}\) and \(M=e^{-L_*P}\). In particular \(M=\overline P\), and the scalar return multiplier is

\[
-L_*^2PM=1.
\tag{5.4}
\]

Thus \(p=P\) supplies the simple parabolic normalization (4.4). The parameter has \(\alpha\ne0,-1\). Corollary 2.2 and affine conjugacy give algebraic independence over \(\mathbb C\) of every finite family

\[
x,F_\alpha(x),\ldots,F_\alpha^{\circ m}(x)
\tag{5.5}
\]

at this distinguished numerical value of \(\alpha\).

**Proposition 5.1 (the Dottie pair is the complete unit-modulus parabolic locus).** Among all multiplier-one fixed points of \(g_L\), the lifted coordinates with \(|\alpha|=1\) are exactly

\[
\alpha=\sin d+id\quad\text{and}\quad\overline\alpha=\sin d-id.
\tag{5.5a}
\]

Their parameters are respectively \(L=ie^{-\sin d}\) and \(L=-ie^{-\sin d}\), and their scalar fixed points are respectively \(P,M\) in (5.3).

*Proof.* By Theorem 4.1, \(\alpha\ne-1\), so choose \(\theta\in(-\pi,\pi)\) with \(\alpha=e^{i\theta}\). Its locus equation becomes

\[
\exp\bigl(2i(\theta+\sin\theta)\bigr)=-1,
\qquad
\theta+\sin\theta=(k+\tfrac12)\pi
\tag{5.5b}
\]

for an integer \(k\). The function \(\theta+\sin\theta\) is odd and strictly increasing on \((-\pi,\pi)\), with range \((-\pi,\pi)\). Consequently the only eligible targets are \(\pi/2\) and \(-\pi/2\), each with one solution. The positive solution lies in \((0,\pi/2)\). Put \(d=\pi/2-\theta\); the equation gives \(d=\sin\theta=\cos d\), so this is the Dottie number. Hence \(e^{i\theta}=\sin d+id\), and the negative solution is its complex conjugate. Formula (4.2a) and the identities (5.2) give the two stated parameters and fixed points. \(\square\)

**Theorem 5.2 (Dottie coefficient arithmetic).** The numbers \(d,s,\alpha\), both phases \(P,M\), and every coefficient \(h_n(\alpha)\) for \(n\ge3\) are transcendental. Also \(\rho=1-h_3\) is transcendental and

\[
\boxed{\mathbb Q(h_3)=\mathbb Q(\rho)=\mathbb Q(s),\qquad
\mathbb Q(h_3,h_4)=\mathbb Q(\alpha).}
\tag{5.6}
\]

*Proof.* Suppose \(d\) were algebraic. It is nonzero, so \(0,id,-id\) are distinct algebraic numbers. The equation

\[
e^{id}+e^{-id}-2d=0
\]

violates their Lindemann–Weierstrass linear independence. Hence \(d\) is transcendental. If \(s\) were algebraic, \(d^2=1-s^2\) would make \(d\) algebraic. Thus \(s\) is transcendental. If \(\alpha\) were algebraic, its complex conjugate would be algebraic, and \(d=(\alpha-\overline\alpha)/(2i)\) would be algebraic. Therefore \(\alpha\) is transcendental.

Proposition 4.3 now gives transcendence of every \(h_n(\alpha)\), \(n\ge3\).

At the Dottie point \(\theta=2s\), so (4.7) becomes

\[
\rho=\frac{s}{3(1+s)},\qquad
s=\frac{3\rho}{1-3\rho}.
\tag{5.7}
\]

These formulas prove the first field equality in (5.6), as well as transcendence of \(\rho\). Proposition 4.2 gives the second equality.

Finally suppose \(P\) were algebraic. Conjugacy makes \(M\) algebraic. Equation (5.4) then makes \(L_*\) algebraic, and \(L_*M\) is a nonzero algebraic number. The exponential \(e^{L_*M}=P\) is transcendental by Lindemann–Weierstrass, a contradiction. The same argument with conjugacy gives transcendence of \(M\). \(\square\)

**Theorem 5.3 (the Dottie field diamond).** Let

\[
K=\mathbb Q(s),\quad A=\mathbb Q(\alpha),\quad
B=\mathbb Q(s,d),\quad C=\mathbb Q(i,\alpha).
\]

Then

\[
[A:K]=[B:K]=2,\qquad A\cap B=K,
\qquad AB=C,\qquad [C:K]=4.
\tag{5.8}
\]

The extension \(C/K\) is Galois with group \(C_2\times C_2\).

*Proof.* Because \(s\) is transcendental, \(K\) is a rational function field over \(\mathbb Q\). The polynomial \(1-s^2\) is a nonsquare in \(K\), as is \(s^2-1\): each has simple zeros at \(s=1,-1\). Therefore the equations

\[
d^2=1-s^2,\qquad \alpha^2-2s\alpha+1=0
\]

define quadratic extensions \(B/K\) and \(A/K\). The field \(B\) is real, while \(A\) contains the nonreal number \(\alpha\); hence \(A\ne B\). Two distinct quadratic extensions have intersection \(K\) and compositum of degree four. They are both splitting fields of separable quadratics, so their compositum is biquadratic and has the stated Galois group.

Since \(\alpha=s+id\), the compositum \(AB\) contains \(i=(\alpha-s)/d\), giving \(C\subseteq AB\). Conversely \(\alpha^{-1}\in A\) and

\[
s=\frac{\alpha+\alpha^{-1}}2,\qquad
d=\frac{\alpha-\alpha^{-1}}{2i}
\]

give \(B\subseteq C\), hence \(AB=C\). \(\square\)

The three intermediate quadratic fields are \(\mathbb Q(s,d)\), \(\mathbb Q(\alpha)\), and \(\mathbb Q(s,i)\). In \(\mathbb Q(\alpha)\), complex conjugation is the reciprocal involution \(\alpha\mapsto\alpha^{-1}\); its fixed field is exactly the cubic-coefficient field \(\mathbb Q(h_3)=\mathbb Q(s)\).

## 6. Algebraic multipliers and a precise Schanuel corollary

This section gives a numerical arithmetic application distinct from the functional theorems. Let \(L\ne0\) and let \((P,M)\) be a reciprocal fixed pair. Its actual lifted coordinates are

\[
U=LM,\qquad V=-LP,
\qquad P=e^U,\quad M=e^V.
\]

They satisfy

\[
UP+VM=0,\qquad \mu=-L^2PM=UV,
\qquad e^{U-V}=-V/U.
\tag{6.1}
\]

**Lemma 6.1.** If \(\mu\) is nonzero algebraic, then \(U,V\) are transcendental and rationally linearly independent.

*Proof.* Both are nonzero. If one were algebraic, \(UV=\mu\) would make both algebraic. If \(U\ne V\), the last equation of (6.1) equates the exponential of a nonzero algebraic number to an algebraic number, contradicting Lindemann–Weierstrass. If \(U=V\), it gives \(1=-1\). Thus both are transcendental. A rational dependence gives \(V=qU\) for some nonzero \(q\in\mathbb Q\), hence \(U^2=\mu/q\), making \(U\) algebraic, again a contradiction. \(\square\)

**Corollary 6.2 (conditional on the Schanuel inequality for \(U,V\)).** Suppose \(\mu\ne0\) is algebraic and

\[
\operatorname{trdeg}_{\mathbb Q}
\mathbb Q(U,V,e^U,e^V)\ge2.
\tag{6.2}
\]

Then \(P,M\) are algebraically independent, and \(U,L\) are algebraically independent. At the Dottie point, (6.2) implies algebraic independence of \(d\) and \(e^{-\sin d}\).

*Proof.* Lemma 6.1 gives the rational independence required by Schanuel's conjecture to imply (6.2). From (6.1),

\[
V=\mu/U,\qquad U^2=-\mu M/P.
\]

Thus adjoining \(U,V\) to \(\mathbb Q(P,M)\) is algebraic after adjoining the algebraic number \(\mu\). The transcendence degree in (6.2) is therefore that of \(\mathbb Q(P,M)\), which is two. Also

\[
P=-\frac{\mu}{LU},\qquad M=\frac UL,\qquad
L^2=-\frac\mu{PM}.
\]

These identities transfer transcendence degree two to \(\mathbb Q(U,L)\). At Dottie, \(U=\alpha\), \(L=ie^{-s}\), and

\[
d=\frac{\alpha-\alpha^{-1}}{2i},\qquad
\alpha^2-2id\alpha-1=0.
\]

Adjoining \(i\) preserves transcendence degree and gives an algebraic correspondence between \(\alpha\) and \(d\). The stated independence of \(d,e^{-s}\) follows. \(\square\)

## 7. Proof dependencies and verification

The functional conclusions use Ax's differential theorem and the rank and tower calculations in Sections 2–3. The unconditional numerical conclusions in Sections 4–5 use Lindemann–Weierstrass, elementary algebra of rational functions, and explicit quadratic extensions. Section 6 retains (6.2) as its named additional hypothesis.

The accompanying [independent verification script](review/independent_checks.py) performs new exact symbolic checks of the Jacobian, ODE, affine normalization, Touchard coefficient formulas, recovery denominators, and the Dottie field equations. It checks composition coefficients through order 14 and Touchard derivative identities through order 8; its precise output is recorded in [independent-checks.json](review/independent-checks.json), with a [mathematical review](review/mathematical-review.md). This script uses exact symbolic arithmetic. The analytical arguments above supply the all-order and arbitrary-depth statements.

## References and provenance

1. James Ax, **On Schanuel's Conjectures**, *Annals of Mathematics* **93** (1971), 252–268. [Publisher record](https://annals.math.princeton.edu/1971/93-2/p03). Original publisher metadata and abstract were accessible during the project; the full-text endpoint returned an application shell.
2. Jonathan Kirby, **Variants of Schanuel's conjecture**, author manuscript, 2018, especially Theorem 5.1. [Full text](https://pure.uea.ac.uk/ws/portalfiles/portal/129743769/1801.08765v1.pdf). This supplies an accessible precise differential statement of Ax's theorem.
3. Samit Dasgupta, **Ranks of matrices of logarithms of algebraic numbers I: the theorems of Baker and Waldschmidt–Masser**, 2023, Section 3. [Author text](https://sites.math.duke.edu/~dasgupta/papers/Baker.pdf). The differential proof of Ax's theorem supplies complementary theorem-and-proof provenance.
4. Michel Waldschmidt, **Schanuel's conjecture**, 2014 survey. [Author text](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/ColloquiumDeGiorgiSchanuelConjecture2014.pdf). Used for the classical transcendence statements and the numerical Schanuel framework.
5. Nick's supplied **Dottie Parabolic Quantization Preprint v0.4**, internally dated 7 August 2026. [Preserved source PDF](sources/Dottie_Parabolic_Quantization_Preprint_v0.4.pdf). Source of the distinguished parameter and normalized Touchard germ studied here.
6. Nick's supplied **Reciprocal Tetration Logarithmic Lift Preprint**, supplied filename v0.10, internal title draft v0.9, 6 August 2026. [Preserved source PDF](sources/Reciprocal_Tetration_Logarithmic_Lift_Preprint_v0.10.pdf). Source of the reciprocal fixed-pair and lifted-logarithm setting.
7. **CARL Transcendence Research**, 15 November 2026. Preserved copies of its [functional report](sources/ax-functional-report.md), [dynamics report](sources/dynamics-products-report.md), and [coefficient/field report](sources/coefficient-fields-report.md) accompany this note. These record the broader research context from which the focused continuation was developed; the original full package retains its experiment records and certificates.
