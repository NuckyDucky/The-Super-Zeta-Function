# The Fourier transform of the quartic signs on the Gaussian lattice

Write $\delta=A+iB=-5045155+1027708i$, $D=N(\delta)=26509772707289$, and $\chi=(\cdot/D)$. The three local residues of the original quartic combine to

$$
r=-A/B\bmod D=11825711960877,\qquad
r^2=-1\bmod D,\qquad
f(a,b)=\eta((a+bi))=\chi(a+rb).
$$

Here $f(0,0)=0$. The earlier norm-73 readings are $f(3,8)=-1$, $f(3,-8)=+1$. These signs specify one of the two conjugate branch conventions.

## Which frequencies survive the signed sum?

Use the unnormalized finite Fourier transform on $(\mathbb Z/D)^2$ with phase $e^{2\pi i(ha+kb)/D}$. Substitution $u=a+rb$ gives

$$
\widehat f(h,k)=
\left(\sum_u\chi(u)e^{2\pi i h u/D}\right)
\left(\sum_b e^{2\pi i(k-rh)b/D}\right)
=D\sqrt D\,\chi(h)\,\mathbf1_{k=rh\bmod D}.
$$

The second factor is elementary character orthogonality. The first is the Gauss sum for a primitive quadratic character of positive fundamental discriminant $D$. In particular it vanishes at nonunits $h$, including at $h=0$. The negative Fourier phase gives the same formula because $\chi(-1)=1$. [Montgomery and Vaughan, Chapter 9, Gauss sums](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf)

The integer pairs satisfying the congruence are exactly the lattice with basis $(A,B)$, $(-B,A)$. Both generators satisfy the congruence, and both descriptions have index $D$ in $\mathbb Z^2$. For $(h,k)=(Au-Bv,Bu+Av)$ one has

$$
h^2+k^2=D(u^2+v^2),\qquad
\chi(h)=\chi(A)\chi(u-rv)=\chi(u-rv).
$$

Indeed $Ar=B\bmod D$, and the three residue signs of $A$ are $+,-,-$. Thus the active frequencies form the subset with nonzero sign on a rotated lattice, and the shortest active vector after dividing both coordinates by $D$ has length $1/\sqrt D\approx1.94221363\times10^{-7}$. This gap is in the Fourier frequencies for the generator coordinates.

For $t>0$ let $\Theta(t)=\frac14\sum_{a,b}f(a,b)e^{-\pi t(a^2+b^2)}$. Summing the Gaussian over residue classes modulo $D$, applying Poisson summation, and inserting the finite transform gives

$$
\Theta(t)=\frac1{t\sqrt D}\,\Theta\!\left(\frac1{Dt}\right).
$$

The substitution $v\mapsto-v$ in the full sum exchanges the two conjugate branch conventions. At $\Re s>1$, the Mellin transform of $\Theta$ is $\pi^{-s}\Gamma(s)L_{\mathbb Q(i)}(s,\eta)$. Hence this dual calculation recovers the reflection of the completed factor. It also exhibits the exact arithmetic cancellation of its constant Fourier mode. The existence of a gap between spatial frequencies gives no lower bound for this Mellin transform at an individual complex $s$.

Alpöge's source proves Poisson summation for any ideal-periodic coefficient function over a totally complex number field. Its hypotheses fit $K=\mathbb Q(i)$, the one complex place, angular weight zero and period ideal $(\delta)$. The preceding formulas determine the dual coefficients that are existential in the theorem statement. The positive sign on the primitive Gauss sum enters the specialization by the classical evaluation. The resulting formulas are derived here on paper. [Hecke kernel theorem, lines 163–169](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeThetaKernelPoissonSummation.lean#L163) · [Primitive Gauss sum product](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussSumMulGaussSumInvOfIsPrimitive.lean#L11)

## The marked angular spectrum on the dual lattice

The angular character from the original marked spectrum is $\omega((z))=(z/|z|)^4$. Four is the smallest positive angular power invariant under changing the generator by any of $1,i,-1,-i$. To recover its Mellin kernel put

$$
H(t)=\tfrac14\sum_{z=a+bi}f(a,b)z^4 e^{-\pi t|z|^2}.
$$

The Fourier transform of $z^4e^{-\pi t|z|^2}$ at complex frequency $\xi$ is $t^{-5}\xi^4e^{-\pi|\xi|^2/t}$. This follows by differentiating the Gaussian four times with the complex derivative $\partial_{\xi_1}+i\partial_{\xi_2}$; that derivative kills $\xi_1+i\xi_2$. On the supporting lattice $\xi=\delta(u+iv)/D$. Conjugation exchanges $f(u,v)$ with $f(u,-v)$, giving

$$
 H(t)=\frac{\delta^4}{D^{9/2}t^5}\,\overline{H(1/(Dt))}.
$$

After the Mellin shift by $2$, the sum is the angular Hecke function $W_\eta(s)=L(s,\eta\omega)$. Its completed functional equation has phase multiplier

$$
\varepsilon_\eta=\frac{\delta^4}{D^2}
=\frac{487698715971699860277988721-505996929954869083445428560i}
{702768048992124756473729521}.
$$

At balanced smoothing $t=1/\sqrt D$, the identity forces every nonzero $H(t)$ onto the straight line of angle $2\arg\delta=-0.4019051933751\bmod\pi$. The conjugate quartic branch reflects that line. The identity also allows $H(t)=0$; the [direct full-conductor sum](angular/README.md) settles its sign and size for this branch. At norm 73 the $z^4$ shell is exactly $+10560i$, reproducing the earlier normalized angular coefficient $+10560i/5329$. The scalar Gaussian series sums those same two signs to zero. The sign and conjugation conventions were checked independently at both local factors 41 and 457 for three positive scales each. [Original marked character and its norm-73 coefficient](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/main/archive/2026-11-20-gaussian-branch-spectrum-v001/README.md)

The same direction test applies at every height on the critical line. With $\Lambda_W(s)=(\sqrt D/\pi)^s\Gamma(s+2)W_\eta(s)$, Mellin transformation gives

$$
\Lambda_W(s)=\varepsilon_\eta\,\overline{\Lambda_W(1-\bar s)}.
$$

At $s=1/2+iT$, the point $1-\bar s$ equals $s$. Hence every nonzero completed angular reading lies on the line of angle $-0.4019051933751\bmod\pi$ for this branch. The other branch gives $+0.4019051933751\bmod\pi$. A single nonzero complex reading in this specified completion and oriented coordinate frame distinguishes the branches even when the sign along the line is hidden. The value zero belongs to both lines. This angular test identifies a branch and supplies no excluded region for the scalar factor.

## What an extra average controls

At a single norm, conjugation can reverse the sign. Over all additive translations there is an exact correlation. If the two translated linear coordinates differ by $d$,

$$
\sum_{u\bmod D}\chi(u)\chi(u+d)
=\prod_{p\mid D}\begin{cases}p-1,&p\mid d,\\-1,&p\nmid d.\end{cases}
$$

For each $p\nmid d$, the local sum is $-1$ since each pair $y^2=x(x+d)$ corresponds to a factorization $(2x+d-2y)(2x+d+2y)=d^2$, giving $p-1$ pairs. The Chinese remainder theorem multiplies the three local sums. For the two conjugate addresses $3\pm8i$, $d=16r$ is coprime to $D$. Their signed correlation over all $D$ translations is therefore exactly $-1$, compared with the squared norm $\varphi(D)=25806599447040$. This is full-period orthogonality information about translations. A sum over a *fixed* narrow ring depends on which translates its changing radial weight selects.

## A check on the time scale of a dual calculation

More generally Poisson transforms a smooth compactly supported radial weight $W(x)$, $x=|z|^2$, into the Hankel integral

$$
\pi\int_0^\infty W(x) J_0(2\pi\sqrt{m x/D})\,dx
$$

at dual norm $m$, with the overall factor $D^{-1/2}$ after replacing the dual coefficients by the original signed ones. For $W(x)=w(x/X)x^{-iT}$, the two oscillatory phases in the large-argument Bessel expansion give a stationary point near $m=(T/\pi)^2D/X$ for $x\approx X$. This estimates the center of oscillatory mass for this probe, with no uniform error asserted. With the project's $T_D=4.52611932248\times10^{12}$, the balance scale $T_D\sqrt D/\pi$ is $7.41786847214\times10^{18}$, and $X=2^{28}$ corresponds to a dual norm around $2.05\times10^{29}$. A direct term-by-term dual sum is unattractive at that cutoff. Bounds for the signed transformed sum could still sharpen the arithmetic tail. The existing approximate functional equation already uses the same balance scale.

## Lattice ratios, class characters and the logarithm sheet

For the imaginary quadratic field $F=\mathbb Q(\sqrt{-D})$, Alpöge's $\mathrm{class\_sum}$ evaluates each individual ideal class's Dirichlet series as a real Eisenstein sum with its ideal lattice ratio for real $s>1$. Its hypotheses allow composite discriminant, unlike the nearby Chowla–Selberg wrapper for prime discriminant. The project's upper-half-plane inverse supplies an ordered exponential fixed pair for every such ratio. For the binary forms of leading coefficients 1 and 13 used in the class calculation these ratios may be taken as $i\sqrt D$ and $(5+i\sqrt D)/13$, since $5^2+D=0\bmod13$. The exact form norm is $a|m+n\tau|^2$, so the leading coefficient $a$ is part of the normalization. [Class sum, lines 322–328](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L322) · [Inverse for the tower](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/main/lean/SuperZeta/DedekindLift.lean#L42)

For buckets $A_j(n)$ indexed by the cyclic class quotient $j=0,1,2,3$, let $B_k=\sum_j i^{jk}A_j$. Orthogonality gives $A_j=\frac14\sum_k i^{-jk}B_k$. At norm 9 the class counts $(1,0,2,0)$ give $(B_0,B_1,B_2,B_3)=(3,-1,3,-1)$. Conjugation gives $A_1=A_3$, so $B_1=A_0-A_2$ reads the signed Gaussian coefficient in the class model tested through norm 4096. The projector is exactly the cyclic specialization of column orthogonality. Knowing the total $B_0$ and the quadratic character $B_2$ gives $A_0+A_2$. It still leaves their difference undetermined. [Column orthogonality](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SumIrrCharOneMulIrrCharColumnOrthogonality.lean#L25) · [Class arithmetic checks](class_check_results.txt)

The tower supplies $V=d/(1-\tau), U=\tau V$ with $e^d=-\tau$. Its two sheets $d=-i\pi/2$ and $3i\pi/2$ at $\tau=i$ scale both ordered exponents by $-3$. The complete normalized lattice, its arithmetic signs and every coefficient of the preceding radial theta series agree on the two sheets. The matrix Iwasawa formula decomposes the lattice shape and a rotation/dilation and does not carry an integral choice of logarithm. Using $e^{d/4}$ would retain that choice modulo four, but identifying the resulting value with the class of an ideal would require an additional arithmetic rule. [Ordered log sheets](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/main/lean/SuperZeta/DedekindLift.lean#L12) · [Matrix decomposition, line 87](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L87)

The Iwasawa *tower* named in item 19 of Alpöge’s historical note has a different arithmetic definition. At its order-four stage the group is $(\mathbb Z/16)^\times/\{\pm1\}$, and its Frobenius depends on the rational prime modulo 16. The two primes $5=2^2+1^2$ and $149=10^2+7^2$ are both $5\bmod16$. Our two Gaussian signs are $(+,+)$ at 5 and $(-,-)$ at 149, so their quartic character traces are opposite. This pair rules out identifying the two order-four measurements on primes by relabeling. Items 15–16 concern an integral structure across characters and approximate orthogonality in an automorphic trace estimate. The exact orthogonality in the generator coordinates above is a separate instance with explicitly known inputs. In particular, the compact trace formula requires a trace-class integrated representation on a compact quotient, while the finite class projector is a directly computable four-term sum. [Alpöge’s note, p. 4](https://alpo.ge/remark.pdf#page=4) · [Cyclotomic Frobenius](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Formalism/BehrendSets/Statement.lean#L9) · [Compact trace formula](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/GroundTheory/AutomorphicForms/TraceFormulaCompact.lean#L112)

The [standalone integer check](check_quartic_dual_theta.py) verifies every frequency of the conductor-41 component and ten on/off-line frequencies of the conductor-457 component in the exact cyclotomic algebra. It checks the actual full-conductor dual norm and character on 6,561 points, without enumerating its full period.

[QuarticDualLine.lean](QuarticDualLine.lean) was checked directly with Lean 4.33.1 and the mathlib cache used by the submission. Its four declarations prove the two-variable factorization for every finite modulus and coefficient function, identify the surviving coefficient in terms of the primitive Gauss sum under explicit primitivity hypotheses, identify the actual one-coordinate quartic weight with the three original residue symbols at every pair of integer coordinates, and prove exact cancellation at every off-line Fourier frequency of that actual modulus. Each listed axiom audit returned only propext, Classical.choice and Quot.sound. The signed evaluation of the primitive Gauss sum, Poisson specialization, angular root number, and resulting phase lines are the mathematical derivation above; this Lean file verifies the finite Fourier steps. The full scalar Gaussian count on the Dottie disk remains open.
