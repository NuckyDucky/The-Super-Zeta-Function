# The Dottie cylinder has a prime-adic phase cover

This construction equips the existing Dottie Fatou cylinder with all prime-power
deck phases simultaneously. Its fibers are p-adic integers. The physical
antiholomorphic half-step becomes an adding machine on a paired fiber, and every
selected horn lift extends compatibly to the whole covering tower.

The general inverse-limit and solenoidal constructions are classical. Relevant
primary sources include [Burgos–Verjovsky, *Adelic solenoid I*, §§2–3](https://arxiv.org/pdf/1603.05676)
and [Sullivan, *Solenoidal manifolds*](https://www.journalofsing.org/volume9/sullivan.pdf).
Here the input is the exact Dottie half-step and the actual deck-count convention
already retained in NuckyDucky's manuscript. The following specialization and its
clock/horn consequences are derived explicitly.

## 1. The exact Dottie gauge

Put \(d=\cos d\), \(s=\sin d\), \(\alpha=s+id\), and
\[
\varkappa=\frac{2\alpha}{1+\alpha}=1+i\beta,
\qquad\beta=\frac d{1+s}.
\]
NuckyDucky's normalized germ and physical square root are
\[
f(x)=\frac{1+\alpha}{2\alpha}
\operatorname{expm1}\left(\alpha\operatorname{expm1}
\left(\frac{2x}{1+\alpha}\right)\right),
\quad K(x)=\frac{\operatorname{expm1}(\varkappa\bar x)}{\varkappa},
\quad K^2=f.
\]
On the selected compatible Fatou charts, the existing normalization has
\[
\Phi(f(x))=\Phi(x)+1,\qquad
\widehat K(W)=\bar W+\varkappa/2.
\]
Make the explicit gauge change
\[
\boxed{W_0=W-i\beta/4.}
\]
Then
\[
\boxed{T(W_0)=W_0+1,\qquad J(W_0)=\bar W_0+1/2,
\qquad J^2=T.}\tag{1}
\]
Indeed the constant changes by \(-i\beta/4-\overline{-i\beta/4}=-i\beta/2\).
In \(\eta=e^{2\pi iW_0}\), equation (1) is
\[
\boxed{j(\eta)=-1/\bar\eta.}\tag{2}
\]
NuckyDucky's original cylinder coordinate \(\xi=e^{2\pi iW}\) has
\(j(\xi)=-r/\bar\xi\), \(r=e^{-\pi\beta}\); thus
\(\eta=\xi/\sqrt r\). This states the gauge transformation explicitly.

The map (2) is fixed-point free and exchanges the two ends \(0,\infty\).
In additive coordinates it reverses Ecalle height and translates real phase by
one half. These are the two marked cylinder ends underlying the two local horn
charts.

## 2. The inverse-limit proposition

Fix a prime \(p\). Set
\[
\mathcal C_k=\mathbb C/(p^k\mathbb Z),\quad k\ge0,
\qquad
\mathcal S_p=\varprojlim_k\mathcal C_k,
\]
where the bonding maps reduce modulo \(p^k\mathbb Z\). In multiplicative
coordinates \(\eta_k=e^{2\pi iW_k/p^k}\), the bonding map is
\(\eta_{k+1}\mapsto\eta_{k+1}^{p}\).

**Proposition.** The following statements hold.

1. The projection \(\mathcal S_p\to\mathcal C_0\) has fiber
   \(\mathbb Z_p\), with exact sequence of topological groups
   \[
   0\longrightarrow\mathbb Z_p\longrightarrow\mathcal S_p
   \longrightarrow\mathbb C/\mathbb Z\longrightarrow0.
   \tag{3}
   \]
   Locally the total space is a complex disk times \(\mathbb Z_p\).

2. It has the concrete presentation
   \[
   \boxed{\mathcal S_p=(\mathbb C\times\mathbb Z_p)/
   ((W,a)\sim(W+n,a-n)),\quad n\in\mathbb Z.}\tag{4}
   \]
   The scalar return acts by
   \[
   [(W,a)]\mapsto[(W+1,a)]=[(W,a+1)].
   \tag{5}
   \]
   On each fiber it is the p-adic adding machine \(a\mapsto a+1\).

3. The physical half-step lifts to
   \[
   \boxed{\mathcal J[(W,a)]=[(\bar W+1/2,a)],\qquad
   \mathcal J^2[(W,a)]=[(W,a+1)].}\tag{6}
   \]
   At finite level it is
   \[
   \boxed{\eta_k\mapsto e^{\pi i/p^k}/\bar\eta_k.}\tag{7}
   \]

4. Choose any base point \(b\in\mathbb C/\mathbb Z\). Its image \(j(b)\)
   is distinct. On the union of the two fibers, suitable origins give
   \[
   \boxed{(0,a)\mapsto(1,a),\qquad(1,a)\mapsto(0,a+1).}\tag{8}
   \]
   The resulting physical clock is
   \[
   \varprojlim_k\mathbb Z/(2p^k\mathbb Z)
   \cong\begin{cases}\mathbb Z_2,&p=2,\\
   \mathbb Z/2\mathbb Z\times\mathbb Z_p,&p\text{ odd},\end{cases}
   \tag{9}
   \]
   with the half-step acting by addition of one.

### Proof

Fix a lift \(W\) of a point in \(\mathcal C_0\). Its lifts to
\(\mathcal C_k\) are \(W+a_k\), \(a_k\in\mathbb Z/p^k\mathbb Z\).
Compatibility is exactly \(a_{k+1}\equiv a_k\pmod{p^k}\). This is the
definition of \(\mathbb Z_p\), proving (3). The map from (4) to the inverse
limit sends \((W,a)\) to \(([W+a_k]_{p^k})_k\). Changing the lift of the
base point by an integer changes \(a\) by its negative, so this map is
well-defined, bijective, and a local product homeomorphism. It preserves the
group law. Equation (5) follows from the stated equivalence relation.

Conjugation preserves integer translations, so (6) respects (4). Squaring adds
one. Equation (7) is its exponential-coordinate expression. Its p-th power
commutes with the bonding map because
\[
\left(e^{\pi i/p^{k+1}}/\bar\eta\right)^p
=e^{\pi i/p^k}/\overline{\eta^p}.
\]

If \(W\) is the chosen origin over \(b\), use \(\bar W+1/2\) as the
origin over \(j(b)\). Then one half-step retains the residue \(a\); the next
adds one, proving (8). At level \(k\), the map
\((\epsilon,a_k)\mapsto2a_k+\epsilon\pmod{2p^k}\) conjugates it to addition
of one. Taking inverse limits gives (9); for odd \(p\), apply the Chinese
remainder theorem. Every finite quotient is one cycle, so the inverse-limit
adding machine has dense orbits. ∎

The transverse metric on a fiber is
\[
d_p(a,b)=p^{-v_p(a-b)}.
\]
Its balls prescribe an increasingly long prefix of low-order digits. Equation
(5) is an isometry for this metric, and every reduction modulo \(p^k\) is a
finite periodic factor. Thus the prime-adic organization is an exact feature of
this constructed phase cover of the Dottie cylinder.

## 3. Horn transitions lift and preserve the deck information

Let a selected additive horn lift satisfy
\[
\mathcal H(W+1)=\mathcal H(W)+1,
\qquad\mathcal H(W)=W+S(e^{2\pi iW}).
\]
For each \(k\), it descends to its domain in \(\mathcal C_k\) because the
same identity holds for every integer translation \(p^k\). Its compatible
multiplicative expression is
\[
\boxed{\mathcal H_k(\eta)
=\eta\exp\left(\frac{2\pi i}{p^k}S(\eta^{p^k})\right).}\tag{10}
\]
The identity \(\mathcal H_{k+1}(\eta)^p=\mathcal H_k(\eta^p)\) follows by
substitution. Equivalently, the lifted map in (4) is
\[
[(W,a)]\mapsto[(\mathcal H(W),a)].
\]
These formulas hold on the inverse image of the selected horn domain.

Changing the additive lift by an integer \(N\) multiplies (10) by
\(e^{2\pi iN/p^k}\); in the fiber it adds \(N\pmod{p^k}\). In particular,
the transition \(T_N(W)=\mathcal H(W)+N\) retains
\[
\boxed{\text{complex horn coordinate, and }N\bmod p^k\text{ at every level}.}
\tag{11}
\]
This is useful for the existing finite-to-horn matching task: a selected
continuation can carry the actual passage/deck count along with its cylinder
point. Two integer counts give the same point on \(\mathcal C_0\), and their
lifts at level \(k\) differ exactly when their residues differ modulo \(p^k\).
Counts in a declared interval shorter than \(p^k\) are distinguished completely
by that residue. Multiple primes combine by the Chinese remainder theorem.

The roles of the three clocks remain explicit: paired period \(p_{\rm pair}\),
scalar period \(p_{\rm pair}/\gcd(p_{\rm pair},2)\), and local deck count
\(N\). Equation (11) records \(N\) during a continued local passage. A finite
period record supplies its own paired and scalar counts. Attaching the records
uses the selected orbit, Fatou chart and continuation gauge.

## 4. Complex fractional time and prime-adic phase share one construction

The leafwise complex translation \([(W,a)]\mapsto[(W+t,a)]\) and the
transverse p-adic translation \([(W,a)]\mapsto[(W,a+u)]\) agree when
\(t=u=n\in\mathbb Z\). Consequently the same object contains the complex
Fatou-time flow and its p-adic completion of integer deck phases. Pulled back
through a chosen petal coordinate, the complex-time action is the usual local
fractional iterate \(\Phi^{-1}(\Phi(x)+t)\).

This construction applies to a simple parabolic germ equipped with a compatible
antiholomorphic square root. Dottie's exact \(\varkappa\), the explicit gauge,
the ordered pair, and the physical period convention make it a concrete model
for the present research program.

## 5. Reproducible checks

`computations/verify_solenoidal_clock.py` proves the finite quotient identities
with exact integers and exhausts all states at selected levels for primes
2,3,5,7. It checks the original-to-unit Dottie gauge and all complex covering,
half-step, square and horn-lift identities at 200 decimal digits. A declared
test displacement \(S(\eta)=1/7+\eta/11+\eta^2/13\) tests the general
functorial formula; its coefficients are explicitly identified in the output.
The script also reads the retained period-639/640/641 certificates and records
their exact paired/scalar clocks and prime-power residues.

The inverse-limit proposition and its horn consequences are proved above. The
finite and numerical checks reproduce their formulas and clock conventions.
