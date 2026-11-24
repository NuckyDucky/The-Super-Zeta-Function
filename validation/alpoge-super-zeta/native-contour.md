# One simple zero read from the Dottie cross-product

I used the same two native words and their previously constructed corrections. I wrote $W=J_--J_+$ and $C=J_-Z_+-J_+Z_-$. In the spectral coordinate $s$ the exact identity is

$$
C(s)=W(s)R(s),\qquad R(s)=\pi^{-2s}(3^{2s}-1)\zeta(2s).
$$

I used the closed disk with center $c=1/4+(7067363/1000000)i$ and radius $r=1/4096$. The numerical replay reconstructs the root from $C'/C$ on the circle. It takes the displayed rational center as input and calls the zeta function and its derivative through $R$. It makes no zeta-zero lookup. [The native identity](native-contact.md) · [The replay](check_native_dottie_contour.py)

## The correction gap across the disk

The gap is $W(s)=P(s)M(s)$, where $P(s)=2s\sin(\pi s)/\pi$. With $u=\log x$ on the positive Mellin ray, I get

$$
M(s)=\int_{-\infty}^{\infty}e^{-2su}
       \log\frac{3+4(\sinh^2 x+x^2)-4x\sinh x}
                {3+4(\sinh^2 x+x^2)+4x\sinh x}\,du,
\qquad x=e^u .
$$

The two determinant values in the ratio are positive on the real ray. Lean checks this single-log formula against the original two kernels and checks the change of variable. The pointwise kernel bounds give $32e^{-|u|}$ as a majorant for the absolute integrand at $c$. Let $m_k$ be the integral of the centered integrand times $(-2u)^k/k!$. On the whole disk Lean then proves

$$
\left|M(s)-\sum_{k=0}^3m_k(s-c)^k\right|\le98304(2r)^4 .
$$

The bound on the exponential Taylor remainder is $|z|^4 e^{|z|}$ with $z=-2(s-c)u$. I use $|z|\le|u|/4$ and $|u|^4\le384e^{|u|/2}$. That leaves the integrable majorant $12288(2r)^4e^{-|u|/4}$, with integral $98304(2r)^4$. If $|m_0|\ge1188/10^9$ and $|m_1|,|m_2|,|m_3|\le5/10^6$, then $|M(s)|>118/10^8$ on the disk. Since $P(s)\ne0$ there, the two corrections are different throughout. [Lean tail and local kernel bounds](NativeDottieMellin.lean) · [Lean Taylor bound and exact center inputs](NativeDottieGapDisk.lean)

The 256-bit Arb replay supplies the four center enclosures. The same replay independently bounds $|W|>11708$ and $|W'|<25255$ on the disk. There is also a direct variation theorem in Lean. If $|W(c)|\ge11700$ and $|W'(s)|\le30000$ on the disk, then $|W(s)|>11690$ there. [Interval output](native-contour-output.txt) · [Lean variation theorem](NativeDottieContour.lean)

## Reading the count and location

For $a=15069-24342i$, the interval replay gives $|C(c)/a|<10^{-6}$ and $|1-C'(s)/a|<0.035$ on the closed disk. Lean uses the weaker derivative bound $1/4$. Then $s\mapsto s-C(s)/a$ contracts the closed disk into its interior. Its fixed point is the unique zero $\rho$ and $C'(\rho)\ne0$. Division by $s-\rho$ gives a holomorphic, nonzero factor throughout the disk, so the weighted circle formula has a single contribution. For an entire weight $\varphi$,

$$
\frac{1}{2\pi i}\oint_{|s-c|=r}\varphi(s)\frac{C'(s)}{C(s)}\,ds
=\varphi(\rho).
$$

The proof is the one-simple-root case of Alpöge's argument. It uses the removable quotient at $\rho$ and Cauchy's formula for the singular term. With weight $1$ I get the count $1$. With weight $s-c$ I get the displacement $\rho-c$ and recover the point by adding $c$. The gap and the nonzero factor of $\zeta(2s)$ identify the recovered zero with the ordinary zeta zero at $w=2\rho$. [Upstream weighted circle proof](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCircleArgumentPrinciple.lean#L19-L85) · [Lean weighted count and location](NativeDottieContour.lean) · [Lean assembly from the center enclosures](NativeDottieGapDisk.lean)

## Recovered point and verification scope

The contour integral encloses

$$
\rho=[0.250000000000000000000000\ \pm 6.73\cdot10^{-25}]
+i[7.067362570867346895228626\ \pm 6.81\cdot10^{-25}].
$$

In particular $7.067362570867346895228625<\Im\rho<7.067362570867346895228627$. The height is about $4.29132653\times10^{-7}$ below the chosen center. It matches the earlier first-zero enclosure at the same spectral input. [Contour output](native-contour-output.txt) · [Earlier first-zero record](native-zero-output.txt)

Lean checks the analytic error bound on the whole disk, uniqueness and simplicity from the contraction inequalities, and the weighted contour identity with the exact location on its right-hand side. The concrete inequalities for the four center coefficients and the cross-product contraction, and the decimal enclosure of the moment, come from the directed Arb replay. They are numeric inputs to the Lean result. [Build, axioms and theorem type](native-contour-lean-audit.txt)

Run the pinned Lean 4.19.0 proof with [replay-native.ps1](replay-native.ps1) using the [existing toolchain instructions](native-contact.md). With python-flint 0.9.0, run:

~~~text
python check_native_dottie_contour.py
~~~
