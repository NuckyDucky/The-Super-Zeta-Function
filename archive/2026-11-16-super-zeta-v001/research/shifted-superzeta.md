# The shifted superzeta: balanced-sign probabilities are its exact pole residues

16 November 2026. This note advances the explicit cosine/Fredholm spectrum
to a shifted superzeta, computes every pole residue, and identifies NuckyDucky's
central-binomial probability inside its analytic structure.

## 1. The current spectrum and its shift

The established reciprocal phase equation and spectral coordinate are
\[
\alpha^2e^{\alpha-\alpha^{-1}}=-1,\qquad
u=(\alpha-\alpha^{-1})/(2i),\qquad\cos^2u-u^2=0.
\]
The auxiliary inverse-cosine coupling u=epsilon cos(u) has the entire
determinant
\[
E_\varepsilon(\lambda)=\cos^2\sqrt\lambda-\lambda/\varepsilon^2.
\]
It is the Fredholm determinant of the inverse square of the previously
constructed boundary operator. Let lambda_j be its zeros, with algebraic
multiplicity. At epsilon=1, they are d² and u_n²,bar(u_n)², n>=1.

For w>=0 and Re epsilon>0 define, initially for Re s>1/2,
\[
\boxed{\mathscr S(s,w;\varepsilon)
=\sum_j(\lambda_j(\varepsilon)+w)^{-s}.}
\tag{1}
\]
Use principal powers. The negative lambda-axis contains no eigenvalue for
these couplings, and adding a nonnegative real w preserves this cut.
Locally in complex w the same definition applies off the rays
-lambda_j-[0,infinity); choose the component continued from w>=0.

The general superzeta viewpoint—Dirichlet functions over an entire zero set,
shifted variables and regularized determinants—is described by
[Voros (2014), §1](https://arxiv.org/pdf/1403.4558). The formulas below are
derived for the specific reciprocal cosine spectrum.

## 2. Complete shifted pole theorem

Put
\[
B_n=\frac{\binom{2n}{n}}{4^n}
=\frac{(1/2)_n}{n!},\qquad n\ge0.
\]

**Theorem.** For nonzero w the meromorphic continuation of (1) has precisely
the simple poles
\[
s=\tfrac12-n,\qquad n=0,1,2,\ldots,
\]
and
\[
\boxed{\operatorname*{Res}_{s=1/2-n}\mathscr S(s,w;\varepsilon)
=\frac{B_nw^n}{\pi}.}
\tag{2}
\]
The residues are independent of epsilon. For w=0 all residues except n=0
vanish, recovering the earlier single-pole theorem. Moreover
\[
\boxed{\mathscr S(-m,w;\varepsilon)=0\quad(m=0,1,2,\ldots),}
\tag{3}
\]
\[
\boxed{\exp[-\partial_s\mathscr S(0,w;\varepsilon)]
=4\left(\cosh^2\sqrt w+w/\varepsilon^2\right).}
\tag{4}
\]

**Proof.** Write
\[
F_\varepsilon(v)=\log\left(1+
v\operatorname{sech}^2\sqrt v/\varepsilon^2\right).
\]
The principal logarithm is holomorphic on Re epsilon>0, locally uniformly
for v>=0. The exact spectral determinant has
\[
\log E_\varepsilon(-v)=2\log\cosh\sqrt v+F_\varepsilon(v),
\]
and
\[
F_\varepsilon'(v)=
\frac{1-\sqrt v\tanh\sqrt v}{\varepsilon^2\cosh^2\sqrt v+v}.
\tag{5}
\]
Both numerator and denominator have removable square-root expressions at zero.

In 1/2<Re s<1 the canonical product and the principal-cut beta integral give
\[
\mathscr S(s,w;\varepsilon)=\frac{\sin\pi s}{\pi}
\int_0^\infty t^{-s}\frac d{dt}\log E_\varepsilon(-w-t)dt.
\tag{6}
\]
Normal interchange follows from the established O(sqrt R) zero count and
the uniform off-cut sector for the large zeros. At large t its derivative is
\[
(t+w)^{-1/2}+O_K(t^M e^{-2\sqrt t})
\]
on parameter compacts, for some fixed M. Hence its full power asymptotic is
\[
t^{-1/2}\sum_{n\ge0}(-1)^nB_nw^nt^{-n}.
\tag{7}
\]
Subtracting any finite number of terms in (7) continues the Mellin integral
leftward. Each term gives (-1)^nB_nw^n/(s+n-1/2), and
sin(pi(1/2-n))=(-1)^n. This proves (2) and completeness of the pole list.
The small-t endpoint is analytic; its integer Mellin poles are canceled by
sin(pi s). Thus no additional poles occur. At the nonpositive integers
the continued integral is regular and the sine factor vanishes, proving (3).

At s=0, differentiate (6). The regularized integral is the finite part of
log E_epsilon(-w-T)-log E_epsilon(-w) as T tends to infinity, after
subtracting 2sqrt(T). Since
log E_epsilon(-w-T)=2sqrt(T+w)-log4+o(1), its value is
-log4-log E_epsilon(-w). This gives (4). The uniform endpoint estimates
also prove holomorphic coupling dependence and the stated local continuation
in w. ∎

This identifies the exact balance coefficient in the superzeta itself:
\[
\boxed{B_n=\frac\pi{w^n}
\operatorname*{Res}_{s=1/2-n}\mathscr S(s,w;\varepsilon),\quad w\ne0.}
\tag{8}
\]
For 2n independent equiprobable signs, B_n is exactly the probability of n
plus signs and n minus signs. Two independent streams give B_n².

## 3. An explicit Bessel continuation

Let w>0. The reference half-integer Laplacian spectrum gives
\[
\mathscr S(s,w;\varepsilon)=\mathscr S_{\rm ref}(s,w)
+\mathscr J_w(s;\varepsilon),
\]
\[
\boxed{\mathscr J_w(s;\varepsilon)=\frac{\sin\pi s}{\pi}
\int_0^\infty t^{-s}F_\varepsilon'(w+t)dt.}
\tag{9}
\]
The integral converges for Re s<1 and continues to an entire s-function by
small-endpoint subtraction. Its derivative at zero is -F_epsilon(w).

Poisson summation of the half-integer Gaussian gives
\[
\boxed{\mathscr S_{\rm ref}(s,w)=
\frac{\Gamma(s-1/2)}{\sqrt\pi\,\Gamma(s)}w^{1/2-s}
+\frac4{\sqrt\pi\,\Gamma(s)}
\sum_{m\ge1}(-1)^m
\left(\frac m{\sqrt w}\right)^{s-1/2}
K_{s-1/2}(2m\sqrt w).}
\tag{10}
\]
The K-series converges normally on every compact s-set. The gamma quotient
contains exactly the poles (2); the winding series and (9) are entire.
This supplies both an independent residue derivation and a rapidly convergent
calculation at positive shifts.

For the K-series tail after m=M, put sigma=Re s, c=2sqrt(w), a=sigma-1,
and assume c>max(a,0)/(M+1). The integral representation of K gives
\[
|K_{s-1/2}(2m\sqrt w)|\le
\sqrt{\frac\pi{m\sqrt w}}e^{-2m\sqrt w}
\exp\left(\frac{(\sigma-1/2)^2}{4m\sqrt w}\right).
\]
Consequently the omitted reference contribution is at most
\[
\boxed{\frac{4w^{-\sigma/2}}{|\Gamma(s)|}
e^{(\sigma-1/2)^2/[4(M+1)\sqrt w]}
\frac{(M+1)^{\sigma-1}e^{-2(M+1)\sqrt w}}
{1-e^{-2\sqrt w+\max(\sigma-1,0)/(M+1)}}.}
\tag{11}
\]
The bound uses cosh(t)>=1+t²/2 and a Gaussian integral to estimate K,
followed by a geometric majorant for the tail powers.

An equivalent single-integral formula is efficient for directed computation.
Set Q_epsilon(v)=cosh²sqrt(v)+v/epsilon² and
\[
H_\varepsilon(v)=\frac{d}{dv}\log Q_\varepsilon(v)-v^{-1/2}
=\frac{\varepsilon^{-2}(1-\sqrt v)
-(1+e^{-2\sqrt v})/(2\sqrt v)}{Q_\varepsilon(v)}.
\]
Then, for w>0 and Re s<1 by continuation,
\[
\boxed{\mathscr S(s,w;\varepsilon)=
\frac{\Gamma(s-1/2)}{\sqrt\pi\,\Gamma(s)}w^{1/2-s}
+\frac{\sin\pi s}{\pi}\int_0^\infty t^{-s}H_\varepsilon(w+t)dt.}
\tag{11a}
\]
The integral has an exponential tail; its positive-integer endpoint poles
are canceled by the sine as before. For real epsilon>0, t=x² and x>=T>=1,
the absolute tail of the integral is at most
\[
8\left[\frac{1+w}{\varepsilon^2}+\frac1{\sqrt w}\right]U_{1-2\sigma}(T)
+\frac8{\varepsilon^2}U_{2-2\sigma}(T),
\quad
U_a(T)=\frac{T^ae^{-2T}}{2-\max(a,0)/T},
\]
provided each denominator is positive. This follows from sqrt(w+x²)<=x+w
and cosh²sqrt(w+x²)>=exp(2x)/4. At s=0 the same integral certifies
\[
\int_0^\infty H_\varepsilon(w+t)dt
=2\sqrt w-\log(4Q_\varepsilon(w)).
\tag{11b}
\]

The retained directed verifier uses u=sqrt(w+t) to avoid a complex
square-root callback at the endpoint. For T>max(1,sqrt(w)) put
\[
C_\sigma(T,w)=
\begin{cases}(1-w/T^2)^{-\sigma},&\sigma>0,\\1,&\sigma\le0.\end{cases}
\]
The absolute omitted integral beyond u=T is bounded by
\[
\boxed{8C_\sigma(T,w)\left[
\varepsilon^{-2}\{U_{1-2\sigma}(T)+U_{2-2\sigma}(T)\}
+U_{-2\sigma}(T)\right].}
\tag{11c}
\]
Indeed |H_epsilon(u²)|<=4e^(-2u)[epsilon^-2(1+u)+1/u].
Multiply by 2u(u²-w)^(-sigma) and integrate each power with the
displayed U bound. Near u=sqrt(w), the further substitution
u=sqrt(w)+q^4 makes the tested quarter-integer endpoint powers
nonnegative integers. The JSON records label the cutoff u=120.

## 4. Shift differentiation and exact resolvent traces

Normal differentiation in the defining half-plane, followed by continuation,
gives
\[
\boxed{\partial_w^k\mathscr S(s,w;\varepsilon)
=(-1)^k(s)_k\mathscr S(s+k,w;\varepsilon).}
\tag{12}
\]
Put Q_epsilon(w)=cosh²sqrt(w)+w/epsilon². Equation (4) yields
\[
\mathscr S(1,w;\varepsilon)=Q_\varepsilon'(w)/Q_\varepsilon(w),
\]
\[
\boxed{\mathscr S(m,w;\varepsilon)=
\frac{(-1)^{m-1}}{(m-1)!}\partial_w^m\log Q_\varepsilon(w),\quad m\ge1.}
\tag{13}
\]
In particular
\[
\mathscr S(1,w;\varepsilon)=
\frac{\sinh(2\sqrt w)/(2\sqrt w)+\varepsilon^{-2}}
{\cosh^2\sqrt w+w\varepsilon^{-2}}.
\]
The numerator is continued at w=0. The elementary determinant thus supplies
every shifted positive-integer trace by differentiation.

The relative correction's stationary numerator in (5) vanishes precisely at
v=nu² with nu tanh(nu)=1. This is the same Laplace critical equation in
the published inverse-cosine framework. It also controls the convergent
multiple-zeta expansion in the companion note.

## 5. The exact link to NuckyDucky's new normalization

The radius law R_n~2pi n and Stirling give B_n²~1/(pi n). Equation (8)
now places that same coefficient inside the superzeta:
\[
\boxed{\frac{R_n}{2}
\left[\frac\pi{w^n}
\operatorname*{Res}_{s=1/2-n}\mathscr S(s,w;\varepsilon)\right]^2
=\frac{R_nB_n^2}{2}\longrightarrow1.}
\]
The finite-n product of these terms has a precise Barnes normalization,
proved separately in this package. The pole index here is the residue order;
the radius index is the quartet level. Their matched-n expression above
is the specified normalization observable connecting the two sequences.

The Hadamard square of the normalized residues is an elliptic period. Its
positive measure, circle-chord model, modular representation and fast
evaluation are developed in `residue-period-and-chords.md`.
