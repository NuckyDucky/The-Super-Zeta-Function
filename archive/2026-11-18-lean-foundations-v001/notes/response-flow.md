# A polynomial response flow and a certified continuation chart at Dottie

This note develops the reciprocal fixed equations into a differential continuation method. The inputs are Nick's ordered fixed pairs and normalized germ, together with the inverse-function coordinate treated in the 2024 spherical-Bessel framework. The resulting statements are a closed response system, an exact Taylor radius, all-order polynomial recurrences, a quantitative two-sheet continuation neighborhood, and certified approximation-error bounds.

## 1. Dynamical observables obey a closed differential system

Let a branch of reciprocal fixed pairs satisfy

\[
P=e^{LQ},\qquad Q=e^{-LP},\qquad L\ne0.
\]

Use the actual exponents

\[
U=LQ,\qquad V=-LP,\qquad a=(U+V)/2,\qquad \mu=UV.
\]

For a local logarithmic parameter \(t=\operatorname{Log}(L/L_0)\), differentiate the fixed equations. Since \(P=e^U\), \(Q=e^V\),

\[
U_t=U(1+V_t),\qquad V_t=V(1+U_t).
\]

Solving the two linear equations gives

\[
\boxed{U_t=\frac{U(1+V)}{1-\mu},\qquad
V_t=\frac{V(1+U)}{1-\mu},}
\]

and hence the closed system

\[
\boxed{a_t=\frac{a+\mu}{1-\mu},\qquad
\mu_t=\frac{2\mu(1+a)}{1-\mu}.}
\tag{1}
\]

These are identities on every regular fixed-pair branch with \(\mu\ne1\). Eliminating \(a\) gives the scalar equation

\[
\boxed{\mu(1-\mu)\mu_{tt}-\mu_t^2-\mu\mu_t+2\mu^2=0.}
\tag{2}
\]

Indeed \(a=(1-\mu)\mu_t/(2\mu)-1\); differentiating this formula and using (1) proves (2). Initial data retain the original exponential fixed equations. The polynomial flow below preserves those equations exactly.

## 2. A regular polynomial flow through multiplier one

Introduce a new local variable \(\zeta\) through

\[
\boxed{\frac{dt}{d\zeta}=1-\mu.}
\]

System (1) becomes the regular polynomial system

\[
\boxed{a_\zeta=a+\mu,\qquad
\mu_\zeta=2\mu(1+a),\qquad t_\zeta=1-\mu.}
\tag{3}
\]

Its initial-value problem is analytic at \(\mu=1\). More explicitly, put

\[
u=(U-V)/(2i),\qquad U=a+iu,\quad V=a-iu.
\]

Then \(\mu-a^2=u^2\), and (3) implies

\[
(\mu-a^2)_\zeta=2(\mu-a^2),\qquad u_\zeta=u.
\tag{4}
\]

Thus \(u=u_0e^\zeta\). The quotient \(b=a/u\) obeys

\[
\frac{db}{du}=1+b^2.
\]

On the reciprocal fixed-pair leaf its solution is \(b=\tan u\). This recovers

\[
a=u\tan u,\qquad \mu=(u\sec u)^2,
\qquad L=iu\sec u\,e^{-u\tan u}.
\tag{5}
\]

The regularization also has a direct preservation proof. In \((U,V)\), equation (3) is

\[
U_\zeta=U(1+V),\qquad V_\zeta=V(1+U),\qquad
(\log L)_\zeta=1-UV.
\]

Consequently

\[
\frac{d}{d\zeta}\log\left(\frac{Ue^{-V}}L\right)=0,
\qquad
\frac{d}{d\zeta}\log\left(\frac{-Ve^{-U}}L\right)=0.
\]

Physical initial data make both ratios one. They remain one wherever the analytic flow is regular, so \(P=e^U,Q=e^V\) continue to satisfy both original fixed equations. The invariant

\[
\mu e^{-2a}/L^2=-1
\]

is their product relation. This gives a continuation method with a built-in fixed-equation constraint.

At a physical multiplier-one point, \(a\ne-1\): the values \(a=-1,\mu=1\) would force \(U=V=-1\), hence \(P=Q=e^{-1}\); the actual definitions \(U=LQ,V=-LP\) would then give \(U=-V\), a contradiction. Hence \(\mu_\zeta=2(1+a)\ne0\), while \(t_\zeta=0\) and \(t_{\zeta\zeta}=-2(1+a)\ne0\). The response flow passes regularly through the quadratic parameter fold.

## 3. Exact Dottie Taylor radius and all-order recurrences

Let

\[
d=\cos d,\quad d\in(0,1),\qquad c=\sin d,\qquad C=1+c,
\qquad L_*=ie^{-c}.
\]

Normalize \(\zeta=\log(u/d)\) and \(t=\tau=\operatorname{Log}(L/L_*)\). Then

\[
u=de^\zeta,\quad a(0)=c,\quad\mu(0)=1,\quad\tau(0)=0.
\]

The exact solution is

\[
\begin{aligned}
a(\zeta)&=de^\zeta\tan(de^\zeta),\\
\mu(\zeta)&=\left(\frac{de^\zeta}{\cos(de^\zeta)}\right)^2,\\
\tau(\zeta)&=\zeta+\log\frac{\cos d}{\cos(de^\zeta)}-a(\zeta)+c.
\end{aligned}
\tag{6}
\]

**Exact-radius theorem.** The Taylor series at zero of \(a,\mu,\tau,L/L_*\), and both normalized phase responses \(P/P(0),Q/Q(0)\), have common radius

\[
\boxed{\rho=\log\frac{\pi}{2d}
=0.753924869396678223386795921069\ldots.}
\tag{7}
\]

**Proof.** The possible finite singularities in (6) satisfy \(de^\zeta=\pi/2+k\pi\). The nearest is the positive real point \(\zeta=\rho\); all remaining positive zeros give a larger real logarithm, and negative zeros add an imaginary part congruent to \(\pi\). Inside \(|\zeta|<\rho\), \(\cos(de^\zeta)\ne0\), so all selected functions are analytic. At \(\rho\), \(a\) has a nonzero simple pole and \(\mu\) a double pole. Integrating \(\tau'=1-\mu\) gives a nonremovable singularity of \(\tau\). The exponentials defining \(L,P,Q\) have essential singularities there. This proves the exact radius. ∎

Write \(a=\sum A_n\zeta^n\), \(\mu=\sum M_n\zeta^n\), \(\tau=\sum T_n\zeta^n\). Equation (3) gives

\[
\boxed{\begin{aligned}
A_0&=c,&M_0&=1,\\
(n+1)A_{n+1}&=A_n+M_n,\\
(n+1)M_{n+1}&=2M_n+2\sum_{j=0}^n A_jM_{n-j},\\
T_0&=T_1=0,&T_n&=-M_{n-1}/n\quad(n\ge2).
\end{aligned}}
\tag{8}
\]

All \(A_n,M_n\) have nonnegative rational polynomial coefficients in \(c\). For \(n\ge1\), they are divisible by \(C=1+c\). These claims follow by induction from (8). In particular,

\[
\begin{aligned}
\mu(\zeta)&=1+2C\zeta+C(2c+3)\zeta^2
+\frac{C(4c^2+14c+13)}3\zeta^3+\cdots,\\
\tau(\zeta)&=-C\zeta^2-\frac{C(2c+3)}3\zeta^3
-\frac{C(4c^2+14c+13)}{12}\zeta^4+\cdots.
\end{aligned}
\]

## 4. A certified two-sheet complex neighborhood

Define the analytic functions

\[
H(\zeta)=-\frac{\tau(\zeta)}{C\zeta^2}-1,
\qquad \psi(\zeta)=\zeta\sqrt{1+H(\zeta)},
\tag{9}
\]

with their removable values at zero and square-root normalization \(\psi'(0)=1\). From (8), \(H(0)=0\) and every Taylor coefficient of \(H\) is nonnegative.

The companion interval calculation establishes, at \(q=1/4\),

\[
\boxed{h:=H(q)=0.554226368831253034900492276322\ldots<5/9.}
\tag{10}
\]

It uses a rational sign-certified bracket for \(d\), 1024-bit Arb arithmetic, and the exact expression (6). The complete bracket and outward enclosures are retained in the JSON record.

**Quantitative continuation theorem.** The function \(\psi\) has a unique holomorphic inverse \(\zeta=\chi(w)\) on \(|w|<1/6\), with \(|\chi(w)|<1/4\). Therefore every logarithmic target

\[
\boxed{|\tau|<\frac{1+\sin d}{36}
=0.046489223032867078203965165713\ldots}
\tag{11}
\]

has exactly two ordered fixed-pair branches in the chart \(|\log(u/d)|<1/4\), counted with multiplicity at the fold. They are

\[
\boxed{\zeta_\pm(\tau)=\chi\!\left(\pm\sqrt{-\tau/C}\right).}
\tag{12}
\]

**Proof.** On \(|\zeta|\le q\), positivity gives \(|H(\zeta)|\le h<1\). The square root in (9) is analytic and

\[
|\psi(\zeta)-\zeta|
\le q\left(1-\sqrt{1-h}\right).
\]

For every \(|w|<q\sqrt{1-h}\), Rouché's theorem applied to \(\psi(\zeta)-w\) and \(\zeta-w\) gives exactly one zero in \(|\zeta|<q\), counted with multiplicity. Each zero is simple, hence varies holomorphically with \(w\). By (10), \(q\sqrt{1-h}>1/6\). Since \(\tau=-C\psi^2\), equation (12) and the target disk (11) follow. The interval calculation also gives \(|\tau(\zeta)|\le-\tau(q)<1/5\) on the chart, so the exponential \(L/L_*=e^\tau\) introduces no additional logarithmic sheet there. Formula (4) makes the ordered fixed-pair parametrization injective in this chart. ∎

The inverse coefficients are explicit:

\[
\chi(w)=w-\frac{2c+3}{6}w^2
+\frac{4c^2+9c+3}{36}w^3+\cdots,
\]

\[
[w^n]\chi(w)=\frac1n[\zeta^{n-1}](1+H(\zeta))^{-n/2}.
\tag{13}
\]

Because \(M_n\) is divisible by \(C\) for \(n\ge1\), every coefficient of \(H\), \(\chi\), and the scalar responses \(a,\mu,\tau,L/L_*\) composed with \(\chi\) is a polynomial in \(c\) over \(\mathbb Q\). A loop around \(\tau=0\) exchanges the two signs in (12), supplying the local branch permutation with a certified domain.

## 5. Computable Taylor tails and an inverse-defect certificate

Let \(0<q_0<r<\rho\) and truncate (8) at degree \(N\). Positivity gives, for \(|\zeta|\le q_0\),

\[
\begin{aligned}
|a-a_N|&\le a(r)(q_0/r)^{N+1},\\
|\mu-\mu_N|&\le\mu(r)(q_0/r)^{N+1},\\
|\tau-\tau_N|&\le\frac{q_0\mu(r)}{N+1}(q_0/r)^N.
\end{aligned}
\tag{14}
\]

For example, the script takes \(N=80,q_0=1/10,r=1/2\) and certifies these bounds at four real/complex points by fresh direct interval evaluations of (6).

There is also an a posteriori certificate for any approximate inverse. Since \(\chi\) maps \(|w|<1/6\) into \(|\zeta|<1/4\), Schwarz–Pick gives

\[
|\chi'(w)|\le\frac{(1/4)(1/6)}{(1/6)^2-|w|^2}.
\]

If \(|w|\le1/8\), \(|\psi(\widetilde\zeta)|\le1/8\), and \(|\widetilde\zeta|<1/4\), integrating along the segment between \(w\) and \(\psi(\widetilde\zeta)\) yields

\[
\boxed{|\widetilde\zeta-\chi(w)|
\le\frac{24}{7}|\psi(\widetilde\zeta)-w|.}
\tag{15}
\]

This turns a computed residual into a rigorous coordinate error. The multiplier error is at most

\[
2\mu(q)(1+a(q))\,|\widetilde\zeta-\chi(w)|,
\]

and the relative errors in either ordered phase are at most

\[
\exp\!\left((a(q)+\mu(q)+de^q)
|\widetilde\zeta-\chi(w)|\right)-1.
\tag{16}
\]

These derivative bounds follow again from coefficient positivity and convexity of the coordinate disk. The script certifies eight inverse samples, including both sides and complex targets, with coordinate error bounds below \(10^{-65}\). Independent 220-digit point evaluations check the fixed equations and requested target values.

## 6. Parameter response and normalized-germ arithmetic meet

For the specified response coordinate, the fields of the log-lift Taylor coefficients \(T_n\), \(n\ge2\), and multiplier coefficients \(M_n\), \(n\ge1\), are each exactly

\[
\boxed{\mathbb Q(c)=\mathbb Q(h_3).}
\tag{17}
\]

Containment follows from (8), and \(T_2=-1-c\) or \(M_1=2(1+c)\) recovers \(c\). The earlier normalized germ has \(1-h_3=c/[3(1+c)]\), giving the stated equality with its cubic coefficient field.

For the ordered phase response, put \(\alpha=c+id\). Its normalized jets generate

\[
\boxed{\mathbb Q\left([\zeta^n]\frac{P(\zeta)}{P(0)}:n\ge1\right)
=\mathbb Q(\alpha)=\mathbb Q(h_3,h_4).}
\tag{18}
\]

Indeed \(c=(\alpha+\alpha^{-1})/2\) and \(id=(\alpha-\alpha^{-1})/2\), so every coefficient lies in \(\mathbb Q(\alpha)\). Conversely,

\[
P_\zeta(0)/P(0)=1+\alpha
\]

recovers the phase. Thus the same quotient/full-phase arithmetic distinction in the normalized dynamical germ controls the parameter-response series. Equations (17)–(18) refer to the explicitly normalized flow coordinate \(\zeta=\log(u/d)\).

## 7. Reproduction and source roles

Run `verify_response_flow.py`. It writes `response-flow-results.json` and checks:

- Exact derivation of the observable system, scalar ODE and polynomial invariants.
- Exact flow jets through order 12 and inverse-fold jets through order 8.
- A rational bracket for Dottie and certified inequalities (10)–(11) in 1024-bit Arb arithmetic.
- Four degree-80 Taylor-tail comparisons and eight inverse-defect certificates.
- Independent 220-digit fixed-pair evaluations at the selected targets.

The published starting framework is Stoutemyer's 2024 inverse spherical-Bessel family, including \(\varepsilon=-1/y_0(u)\), its inverse branches and stationary values. Nick's fixed equations, Dottie normalization and germ coefficient fields provide the Hidden Work inputs. The polynomial response flow, its exact log-phase series radius, the quantitative inverse chart, the defect certificate and the response-jet field statements are derived and verified in this continuation.

Primary current-work source: [Stoutemyer, 2024, inverse spherical Bessel functions](https://mapletransactions.org/index.php/maple/article/download/16787/16573/55313). The fixed-pair and germ identities are recorded in Nick's supplied reciprocal-tetration and Dottie manuscripts and the earlier focused coefficient note.
