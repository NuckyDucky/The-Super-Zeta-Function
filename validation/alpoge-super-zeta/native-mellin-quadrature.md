# The four Mellin coefficients for the first Dottie contour

I use the same disk centered at $c=1/4+7.067363i$ with radius $1/4096$. The correction gap is $W=J_--J_+$. The numbers below bound the first four Taylor coefficients at $c$ of the Mellin integral before its prefactor. If the eight finite real inequalities hold, Lean gives $|W(s)|>11600$ throughout the closed disk. [Original contour](native-contour.md) · [Lean implication](NativeDottieMellinFinite.lean)

## From the infinite integral to the finite coefficients

If $u=\log x$ and $b=e^{-x}$, I put $t=1-b^2$ and $A=t^2+(3+4x^2)b^2$. The log in the integrand is

$$
\log\frac{A-2xbt}{A+2xbt}.
$$

Multiplying both determinant values by $b^2$ gives the identity on the real line. The coefficient numbered $k$ uses this log times $(-2u)^k e^{-u/2}/k!$ and $\cos(2\Im(c)u)-i\sin(2\Im(c)u)$. If I cut the integral at $a\le0\le d$, Lean bounds the complex error by

$$
\frac{32}{3}4^k e^a+\frac{512}{9}4^k e^{-e^d/2}.
$$

For $k=0,1,2,3$ and $[a,d]=[-32,5]$ this is at most $10^{-11}$. If $m_k^{\rm fin}$ is the corresponding finite integral, the sufficient inequalities in Lean are

$$
\Re m_0^{\rm fin}\le-\frac{11565}{10^{10}},
\qquad
\Im m_0^{\rm fin}\le-\frac{2740}{10^{10}},
$$

$$
|\Re m_k^{\rm fin}|\le\frac{271}{10^8},
\qquad
|\Im m_k^{\rm fin}|\le\frac{405}{10^8},
\qquad k=1,2,3.
$$

Lean checks the real and imaginary integrands and carries the tail bound through to the original correction gap. [Finite integrands](NativeDottieMellinExpression.lean) · [Tail and gap proof](NativeDottieMellinFinite.lean)

## What the panel rule checks

I use a 25-node rational quadrature rule on $[-1,1]$. Lean's kernel checks that its weights are positive, sum to two, and integrate every monomial through degree 24 exactly. If the integrand is holomorphic on a neighborhood of the disk of radius $8h$ about a panel center and its norm is bounded on the circle by $M$, then Lean bounds the error on the real panel of half-width $h$ by

$$
\frac{4hM(1/8)^{25}}{1-1/8}.
$$

The 192-bit Arb replay uses 1,201 panels. It checks that the two determinant values stay in the right half-plane on each enlarged panel, bounds the complex integrand there, and evaluates the 25 nodes of each panel. All eight inequalities pass. The largest summed quadrature error bound is below $9\cdot10^{-20}$, before adding the infinite-tail allowance. The finite node enclosures and the bounds on the enlarged panels come from Arb in this replay. [Lean Cauchy estimate](CauchyPanelQuadrature.lean) · [Exact panel rule](MellinQuadratureRule.lean) · [Arb replay](check_native_mellin_quadrature.py) · [Recorded enclosures](native-mellin-quadrature-output.txt)

## One complex strip for every panel

I put $z=e^u$, $A=3+4(\sinh^2z+z^2)$, and $q=4z\sinh z/A$. On the entire strip $|\Im u|\le1/16$, Lean proves $A\ne0$ and $|q|\le2/3$. For $\Re z\le4$ I bound the arguments of $z$ and $\sinh z$ through their real and imaginary parts. For $\Re z\ge4$ I multiply both determinants by $e^{-2z}$ and bound the terms around $1$. The two expressions give the same $q$.

If $|q|\le2/3$, the logarithms $\log(1-q)$ and $\log(1+q)$ are holomorphic there and their difference has norm at most $8/3$. Lean checks that the resulting complex integrand agrees with the exact Mellin integrand at every real $u$. [Complex strip proof](MellinStripBound.lean)

I divide $[-32,5]$ into 2,368 panels of width $1/64$. The radius-$1/16$ Cauchy circles all fit in the proved strip. The whole integral then differs from the weighted sum by at most $10^{-12}$ for $k=0$ and $10^{-8}$ for $k=1,2,3$. Let $Q_k$ be that sum. If

$$
\Re Q_0\le-\frac{11566}{10^{10}},\qquad
\Im Q_0\le-\frac{2741}{10^{10}},\qquad
|\Re Q_k|\le\frac{270}{10^8},\qquad
|\Im Q_k|\le\frac{404}{10^8}\quad (1\le k\le3),
$$

then Lean gives $|W(s)|>11600$ across the original closed disk. The 192-bit Arb replay supplies the eight weighted-sum inputs. Use `python check_native_mellin_quadrature.py --uniform-strip` for that partition. [Partition and disk theorem](MellinStripQuadrature.lean) · [Directed replay output](native-mellin-strip-output.txt)

At the node $u=0$, my earlier $\widehat\pi$ calculation supplies the Lean bound on $e$. The real Mellin reading is between $-0.789230109860795$ and $-0.789230109860793$, and the imaginary reading is $0$. Lean reduces the log comparison to two exact rational Taylor checks with `decide +kernel`. [Origin sample theorem](MellinOriginSample.lean)

If I replace each real and imaginary node reading of the zeroth density by a rational within $10^{-14}$, the contribution to the error in the $k$th weighted sum is at most $37(64^k/k!)10^{-14}$. The same pair of node readings feeds all four moments. Lean carries eight exact rational comparisons and those node enclosures to the closed-disk gap. The replay checks the proposed node errors with Arb and checks the rational sums with Python's Fraction. [Rational sum theorem](MellinRationalSum.lean) · [Recorded checks](native-mellin-strip-output.txt)

The 17-module replay uses Lean 4.19.0. Run [replay-native.ps1](replay-native.ps1) with the [pinned toolchain and library paths](native-contact.md). Both numerical replays use python-flint 0.9.0. [Current Lean build and axiom audit](native-mellin-strip-lean-audit.txt)
