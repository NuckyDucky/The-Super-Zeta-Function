# The Super Zeta Function

<div><a name="abstract"></a><a name="introduction"></a></div>

I define the super zeta from the fixed pairs of my reciprocal exponential tower. One update sends $(P,Q)$ to $(e^{LQ},e^{-LP})$. I keep both exponents, $U=LQ$ and $V=-LP$, in that order. At a fixed pair the derivative of the two-step return is $UV$. When $UV=1$, the difference $u=(U-V)/(2i)$ satisfies $u=\pm\cos u$. Squaring identifies each pair $u,-u$. The resulting values are the zeros of the determinant $E$, and their inverse powers define the super zeta at unit coupling. [Fixed pairs and their inverse](docs/proofs/quartet-spectrum.md#eq-1)

~~~math
E(v)=\cos^2\!\sqrt v-v,\qquad
\mathcal Z(s;1)=\sum_{E(v)=0} e^{-s\mathrm{Log}\,v},\qquad \Re s>\tfrac12.
~~~

I count each zero with its multiplicity and use the principal logarithm. Comparing $E$ with the half-integer cosine spectrum gives an exact Riemann-zeta factor. The ordered stages also give a way to tell apart two Gaussian primes with the same norm. Their contributions meet in the factorization of my quartic field zeta in chapter 4. [Spectral derivation](docs/proofs/quartet-spectrum.md) · [Field derivation](archive/2026-11-20-dedekind-phase-v001/README.md)

**Results**

- A period-640 return sets three height intervals. I account for all eleven Riemann zeros there on the critical line, sharpening the 7/8ths and Liu bounds in those intervals. [Zero counts and intervals](#4-transferring-zero-results-one-factor-at-a-time)
- The balanced sign counts recover the exact Stirling remainder of a single factorial. The quartet radii determine the sign change between levels 28 and 29. [Factorial identity](archive/2026-11-18-stirling-correction-v001/README.md) · [Comparison with equally spaced radii](archive/2026-11-18-quartet-grid-comparison-v001/README.md)
- The completed angular spectrum distinguishes the two branches of the quartic. Two derivatives of the signed exponential composition recover its ordered stage rates at every nonzero integral lift $L=m\pi i$. [Branch recovery](archive/2026-11-20-gaussian-branch-spectrum-v001/README.md) · [Derivative theorem](archive/2026-11-20-hidden-lift-v001/README.md)

[Full derivations and preprints](docs/proofs/reciprocal-constructions.md) · [Interactive Hurwitz paths](https://nuckyducky.github.io/The-Super-Zeta-Function/) · [Two-input spectral map](https://nuckyducky.github.io/The-Super-Zeta-Function/two-input/) · [Gaussian circle measurements](archive/2026-11-20-gaussian-circle-phases-v001/README.md)

<div><a name="from-the-original-meme-to-the-dottie-spire"></a><a name="the-quadratic-and-the-genus-one-curve"></a><a name="1-the-quadratic-and-the-genus-one-curve"></a><a name="read-quartic" id="user-content-read-quartic"></a><a name="what-the-right-panel-shows"></a><a name="real-ovals-and-projective-completion"></a><a name="the-point-giving-my-approximation-to-π"></a></div>

## The quadratic, the ordered exponential stages and the spectrum

My quadratic supplies the two conjugate factors of a genus-one quartic. The reciprocal tower supplies the ordered exponents $U,V$. At the Dottie fold the two-step derivative equals one. Requiring this same derivative at other complex fixed pairs gives the cosine spectrum in the definition above.

### The two real ovals and the Gaussian quadratic factor

My six coefficients give $N(x)=465x^2-183x-659$ and $D(x)=155x^2+396x-936$.

<details>
<summary>Completing the square and recovering the two branches</summary>

Equating $N/D$ to $(1+y)(2+y)/(y^2+y-1)$ gives a quadratic in $y$. With $A=N-D$ and $Y=2Ay+N-3D$, completing the square gives

~~~math
Y^2=A(x)^2+4N(x)^2=\bigl(A(x)+2iN(x)\bigr)\bigl(A(x)-2iN(x)\bigr).
~~~

The signs of $Y$ give the two real branches. Adding their points at infinity closes each into an oval. I use the discriminant of $A+2iN$ in chapter 2 to distinguish primes of the same norm. [Quartic derivation and diagram of the ovals](docs/proofs/reciprocal-constructions.md#user-content-read-quartic)

</details>

<div><a name="reciprocal-tetration"></a><a name="2-reciprocal-tetration"></a><a name="read-tetration" id="user-content-read-tetration"></a><a name="the-dottie-spire"></a><a name="read-dottie-spire" id="user-content-read-dottie-spire"></a></div>

The figure varies the complex logarithm $L$ while keeping the starting pair $(1,1)$ fixed. Each color gives the period reached in the iteration survey. Gray marks parameters where the iteration limit was reached without identifying a period in the search range. The enlarged region contains the Dottie fold. [Tetration preprint](archive/2026-11-18-lean-foundations-v001/papers/foundations/main.pdf) · [Dottie spire preprint](archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.pdf) · [Sampling limits](archive/2026-11-18-research-figures-v001/README.md)

![Paired periods from the cap in the complex logarithm plane, with the Dottie fold magnified at right.](archive/2026-11-18-research-figures-v001/dottie-spire.png)

<div><a name="the-spectral-zeta-and-the-critical-line"></a><a name="building-the-super-zeta"></a><a name="3-building-the-super-zeta"></a><a name="read-super-zeta" id="user-content-read-super-zeta"></a><a name="1-compose-the-two-marked-stages"></a><a name="31-compose-the-two-marked-stages"></a><a name="2-recover-the-marked-phases-from-the-cosine-roots"></a><a name="32-recover-the-marked-phases-from-the-cosine-roots"></a><a name="3-square-the-roots-and-sum-their-inverse-powers"></a><a name="33-square-the-roots-and-sum-their-inverse-powers"></a><a name="4-compare-with-the-odd-integer-spectrum"></a><a name="35-compare-with-the-odd-integer-spectrum"></a></div>

### How the half-integer spectrum gives the Riemann factor

At $UV=1$, specifying a cosine root and the sign in its equation recovers the ordered exponents and $L$. The determinant product gives $\mathcal Z(1;1)=2$ and $\mathcal Z(2;1)=10/3$.

<details>
<summary>The cosine reference, Mellin correction and multiplicities</summary>

For the comparison determinant $\cos^2\sqrt v$, the zeros $v=\pi^2(n+1/2)^2$ are double. Summing their inverse powers gives the odd-integer part of the Riemann series. On the negative axis the determinant ratio is $1+t/\cosh^2\sqrt t$. Its logarithm gives the Mellin correction $J$, and continuation gives

~~~math
\mathcal Z(s;1)-J(s;1)=2\pi^{-2s}(2^{2s}-1)\zeta(2s).
~~~

The prefactor is nonzero for $0<\Re(2s)<1$. A Riemann zero at $w$ therefore has the same multiplicity in this difference at $s=w/2$. [Product and exact sums](docs/proofs/quartet-spectrum.md#4-canonical-product-and-exact-rational-trace-sums) · [Mellin comparison and continuation](docs/proofs/quartet-spectrum.md#5-a-two-variable-zeta-for-the-inverse-cosine-coupling-family)

</details>

## 1. Arithmetic weights from the two logarithms

The ratio $\tau=U/V$ gives the shape of the lattice $m+n\tau$. Choosing a logarithm $d$ with $e^d=-\tau$ fixes its sheet. For $\Im\tau>0$ I recover $V=d/(1-\tau)$, $U=\tau V$ and $L=Ue^{-V}$. This uses the full fixed-pair family. For instance, the square lattice at $u=\pi/4$ has multiplier $\pi^2/8$. [Inverse in Lean](lean/SuperZeta/DedekindLift.lean)

<details>
<summary><strong>The Eisenstein norm and the prime-power weight</strong></summary>

At $u=\pi/6$ the ordered ratio is $\omega=e^{2\pi i/3}$. The squared length of $m+n\omega$ is $m^2-mn+n^2$. Every nonzero Eisenstein ideal has six generators differing by units, so for $\Re w>1$,

~~~math
\frac16\sum_{(m,n)\ne(0,0)}(m^2-mn+n^2)^{-w}
=\zeta_{\mathbb Q(\sqrt{-3})}(w)=\zeta(w)L(w,\chi_{-3}).
~~~

At $p^j$ the coefficient multiplying $\log p$ in the field’s negative logarithmic derivative is $1+\chi_{-3}(p)^j$. My earlier detector assigned $1+\chi_{-3}(p)^j/7$ to the same prime power. At $2,4,8$ the field weights are $0,2,0$ because the first ideal over 2 has norm 4. With the field weights, 160-bit interval arithmetic gives the one-sided bound $G_K(x)<0.065597\sqrt{x}$ for every real cutoff $6501\le x\le4194304$. [Definition and four-range replay](archive/2026-11-20-dedekind-phase-v001/README.md) · [Quadratic factorization, Aycock and Kobin](https://arxiv.org/abs/2205.06298)

</details>

## 2. A phase hypothesis from my quartic

At $u=\pi/4$ the ordered ratio is $i$, so each Gaussian integer $m+ni$ marks a lattice point. My factor $A+2iN$ has discriminant $\delta=-5045155+1027708i$ and gives the field $E=\mathbb Q(i,\sqrt{\delta})$. I use $k=\mathbb Q(i)$ for its base field. For a Gaussian prime away from the conductor, the sign is $+1$ if it splits into two in $E$ and $-1$ if it stays prime. I asked how much of that sign I could recover from the direction of the marked point. [Derivation from the six coefficients](archive/2026-11-20-dedekind-phase-v001/README.md)

<details>
<summary><strong>Recovering a prime from its direction and testing the sign</strong></summary>

A Gaussian prime of odd rational prime norm has a primitive generator. Its direction modulo $\pi/2$ fixes the reduced slope $n/m$ of the first-quadrant representative. Those integers specify the prime norm and the image $i=-m/n$ in its residue field, where I can factor the quadratic directly. For prime norms at most $X$, angular error below $\tfrac12\arcsin(1/X)$ suffices. For general ideals the direction can lose information. The generators $z$ and $73z$ have the same direction and give opposite signs when coprime to the conductor. [Direction and precision proof](docs/proofs/marked-gaussian-direction.md) · [Residue calculation in Lean](lean/SuperZeta/FieldWeights.lean)

</details>

## 3. Phase tests at conjugate Gaussian primes

At norm 73 the ideals generated by $3+8i$ and $3-8i$ give opposite signs. Reducing the quartic at the first gives no root and at the second gives two. The ordinary coefficient adds the signs to zero. Keeping the positive imaginary direction fixed by the ordered lift lets an angular coefficient distinguish which prime carried the minus. [Conductor and prime checks](archive/2026-11-20-dedekind-phase-v001/README.md) · [Angular coefficient at 73](archive/2026-11-20-gaussian-branch-spectrum-v001/README.md)

### Three residue symbols and the comparisons at 13, 37 and 73

For a nonzero generator $z=m+ni$, the three residue symbols at the primes dividing $(\delta)$ determine its character value.

<details>
<summary>The residue formula and the sign table</summary>

Here $t$ is the image of $i$ modulo the corresponding prime, and a zero symbol marks an ideal sharing a prime with the conductor.

~~~math
\eta_\delta((m+ni))=
\prod_{(p,t)\in\{(41,32),(457,109),(1414835497,516876951)\}}
\left(\frac{m+nt}{p}\right).
~~~

| Norm | Generators in the order tested | Signs |
| ---: | --- | --- |
| 13 | $2+3i,\ 2-3i$ | $-1,\ -1$ |
| 37 | $1+6i,\ 1-6i$ | $+1,\ +1$ |
| 73 | $3+8i,\ 3-8i$ | $-1,\ +1$ |

Multiplying the two signs replaces each numerator by $m^2+n^2$ inside the symbol. The norm thus determines whether the signs agree. At 73 the separate reductions $i=27,46\bmod 73$ assign the signs in order. [Conductor proof and direct checks](archive/2026-11-20-dedekind-phase-v001/README.md)

</details>

### Reading the branch from the completed angular zeros

I weight each ideal by the fourth power of its unit direction. For the zeros $\rho$ of the resulting completed angular function, counted with multiplicity, the value $-\Im\sum_\rho(2-\rho)^{-2}$ is positive for $A+2iN$ and negative for $A-2iN$.

<details>
<summary>Bounding the zero sum and recovering the two signs</summary>

I enclosed it with the differentiated Euler series and a bound on its infinite tail. Lean checks how the zero sum changes under conjugation and relabeling. Reading the two primes above 73 in the same order then gives the words $-+$ and $+-$. [Analytic proof and numerical enclosures](archive/2026-11-20-gaussian-branch-spectrum-v001/README.md) · [Ordered recovery in Lean](lean/SuperZeta/MarkedBranch.lean) · [Conjugation of the zero sum](lean/SuperZeta/ZeroMoment.lean)

</details>

### Lemma. Chronological order of the signed stages

At base 2 the word $-+$ sends $1$ to $1/2$ and then to $\sqrt2$. Reversing the stages gives $1\mapsto2\mapsto1/4$.

<details>
<summary>Inverting a positive real stage</summary>

More generally, for a positive real lift $L$, an endpoint above or below 1 identifies the last sign. Taking its absolute logarithm and dividing by $L$ recovers the preceding value. Repeating this recovers the word all the way to its initial cap. Balanced words with the same number of each sign can therefore give different endpoints. [Six worked examples](docs/proofs/chronological-order.md) · [Lean proof](lean/SuperZeta/SignWords.lean)

</details>

### Recovering the signed stages when the cap values coincide

At $L=\pi i$, all six balanced four-stage words send $1$ to $-1$ and give $W'(1)=\pi^4$. Their second derivatives distinguish all six.

<details>
<summary>Derivative formula and the hidden integral lift</summary>

For a word of length $n$, let $c_j$ be the product of its first $j$ signs. The chain rule gives

~~~math
\frac{W''(1)}{W'(1)}=-\sum_{j=1}^n c_j(-\pi i)^j.
~~~

The highest differing power outweighs all lower differences. At a hidden nonzero integral lift $L=m\pi i$, the first two derivatives determine the ordered stage rates $m\sigma_j$ of any nonempty word. Flipping both $m$ and every sign preserves those rates. One independently labeled odd-stage prime reading distinguishes the two labelings. [Fixed-lift derivation and experiment](archive/2026-11-20-cap-derivative-recovery-v001/README.md) · [Dominance proof](lean/SuperZeta/CapRecovery/Dominance.lean) · [General weights](lean/SuperZeta/CapRecovery/GeneralWeights.lean) · [Hidden-lift proof and experiment](archive/2026-11-20-hidden-lift-v001/README.md) · [Lean classification](lean/SuperZeta/CapRecovery/HiddenLift.lean)

</details>

<div><a name="4-strengthening-the-78ths-and-liu-bounds-in-three-height-intervals"></a><a name="a-local-strengthening-of-the-seven-eighths-theorem"></a><a name="local-zeta-result"></a><a name="a-local-strengthening-of-the-78ths-theorem"></a><a name="4-a-local-strengthening-of-the-78ths-theorem"></a><a name="read-zero-counts" id="user-content-read-zero-counts"></a><a name="how-the-iteration-gives-the-height"></a><a name="selection-of-the-test-height"></a><a name="what-the-three-windows-tell-me"></a><a name="certified-counts-in-the-three-windows"></a></div>

## 4. Transferring zero results one factor at a time

Inside the critical strip the quartic field zeta is a product of three holomorphic functions, so their orders of vanishing add at each point. Writing $\beta_D(w)=L(w,\chi_{-4})$ for Dirichlet beta, the factorization is

~~~math
\zeta_E(w)=\zeta(w)\,\beta_D(w)\,L_k(w,\eta_\delta).
~~~

The eleven Riemann zeros found in the three Dottie windows each contribute at least one to the field count. An exact count for the field also requires the beta and Gaussian factors in those same windows. Near $T_D$, the Gaussian factor is the one I test with the prime signs from chapter 3. [Field factorization](archive/2026-11-20-dedekind-phase-v001/README.md) · [Gaussian endpoint test](archive/2026-11-20-gaussian-endpoint-parity-v001/README.md)

<details>
<summary><strong>How the three factors arise and which zero results transfer</strong></summary>

The Mellin comparison gives the Riemann factor. In the symmetrized Hurwitz reference the shifts are $1/2\pm a/\pi$. Differentiating in $a$ subtracts their contributions. At $a=\pi/4$, the classes $1,3\bmod 4$ enter with opposite signs, giving $\partial_a R(\pi/4,w-1)=(w-1)(4/\pi)^w\beta_D(w)$. At $a=\pi/6$ the corresponding character is $\chi_{-3}$. The third factor uses the square lattice of the lift and the residue signs of my quartic. [Both angular evaluations](archive/2026-11-20-dedekind-phase-v001/README.md) · [Calculation at the first Riemann zero](archive/2026-11-20-dedekind-phase-v001/first-zero.md)

~~~mermaid
flowchart TB
    A["Six coefficients"] --> B["Gaussian quadratic factor"]
    B --> C["Conductor and three residue symbols"]
    U["Ordered exponents U and V"] --> G["Marked lattice point at U/V = i"]
    G --> H["Gaussian Hecke factor"]
    C --> H
    U --> D["Multiplier-one cosine determinant"]
    D -->|"Mellin comparison, w = 2s"| Z["Riemann factor ζ(w)"]
    R["Hurwitz derivative at π/4"] --> J["Dirichlet beta β(w)"]
    H --> F["Quartic field zeta"]
    Z --> F
    J --> F
~~~

At the first positive Riemann zero the derivative of zeta and both additional Dirichlet values are enclosed away from zero. This gives multiplicity one in both quadratic field zetas. In the quartic it gives one plus the order of the Gaussian factor. Liu’s unitary Hecke bound applies to that factor. Taking the Riemann and Dirichlet critical-line conclusions in Sutherland’s report on Alpöge’s submission, any off-line zero of $\zeta_E$ must come from the Gaussian factor with the same multiplicity. [First-zero replay](archive/2026-11-20-dedekind-phase-v001/first-zero.md) · [Liu, Theorem 1.1](https://hexagonmath.org/pdf/2611.00421v1#page=2) · [Sutherland’s verification report](https://math.mit.edu/~drew/grh/) · [Comparison with Masullo’s trace formula](docs/number-fields/masullo-trace-formula.md)

</details>

### Eleven simple Riemann zeros in three Dottie height windows

I chose $T_D\approx4.5261\times10^{12}$ from the marked period-640 return before counting zeros there. In windows centered at $T_D,2T_D,3T_D$ with respective half-widths $1/4,1/2,1/2$, the counts with multiplicity are 2, 5 and 4. Each is a count of distinct simple zeros on the critical line. A simple zero has nonzero first derivative and contributes one to the count.

<details>
<summary>Matching the full count to the critical-line sign changes</summary>

In each window I found that many disjoint intervals on the critical line where Hardy’s real-valued function changes sign. A sign change gives at least one zero in each interval. An additional zero anywhere in the strip or a repeated zero in a bracket would exceed the measured total. This is how the counts sharpen the 7/8ths and Liu bounds at these heights. [Height selection](archive/2026-11-17-dottie-grid-match-v001/README.md) · [Counts, signs and endpoint checks](archive/2026-11-20-liu-angular-velocity-v002/README.md) · [OpenAI, Theorem 1.1](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf)

</details>

### Two inverse branches of the Gaussian factor at the Dottie height

In the polynomial model two solutions of $P(z)=v$ meet at a critical value. For the completed Gaussian factor $f$ I follow solutions of $f(w)=v$ in a rectangle at $T_D$.

<details>
<summary>Nonzero targets, endpoint signs and the remaining count</summary>

Directed arithmetic gives two simple solutions for every real target with $1.05238\times10^{-18}\le |v|\le6\times10^{-16}$. One has real part above $1.018$ and the other below $-0.018$. They lie at the same height and approach each other horizontally as $|v|$ decreases.

At $v=0$ these preimages would be Gaussian zeros. The parity test compares the two real endpoint readings at $T_D\pm1/16$. Cancellation at 404 split primes bounds their magnitudes by $3.584\times10^{-19}$ and $2.945\times10^{-19}$, respectively. Both enclosures include zero, leaving Gaussian parity open. Ordinary zeta has exactly zero zeros in this narrower window. [Inverse branches and contour](archive/2026-11-20-gaussian-two-root-transition-v001/README.md) · [Endpoint values and replay](archive/2026-11-20-gaussian-endpoint-parity-v001/README.md)

</details>

### Spiral phase on the Gaussian circle

I followed the finite Gaussian sum $L_N$ around the right circle at 193 norm cutoffs. Its spiral phase is $\arg L_N-\kappa\log\lvert L_N\rvert$ modulo $2\pi$, with $\kappa$ set by the period-640 return. At every tested cutoff its spiral phase stayed more than $0.91$ radians from $3.9$ on the entire circle. Applying the same phase test on the reflected circle gave two crossings at each cutoff. Both finite sums wound zero times around the origin. The bound on the omitted terms still allows the full Gaussian factor to pass through zero on the boundary, so its winding and the zero count inside remain open. [Circle measurements, radii and remainder bound](archive/2026-11-20-gaussian-circle-phases-v001/README.md)

### The reflected disks and the weight available for an off-line pair

Set $T=T_D-1/512$. Reflection pairs the zeros of the closed disks centered at $31/64+iT$ and $33/64+iT$ with radius $15/1024$.

<details>
<summary>Weight bound, multiplicities and Lean verification</summary>

The total Gaussian zero weight is below $87.057901$. Each zero in either disk costs more than $5.481507$ of that weight. Eight on one side would force eight on the other, contributing more than $87.704112$. This calculation alone bounds each disk by seven, counting multiplicities. The circle phase experiment above uses a slightly larger outer radius of $31/2048$. [Disk derivation and two numerical checks](archive/2026-11-20-gaussian-reflected-disks-v001/README.md) · [Outer-circle experiment](archive/2026-11-20-gaussian-circle-phases-v001/README.md)

Lean checks the lower weight integrand and integration rule, the deduction from the trace inequalities, and a sufficient condition for both disks to be empty. The explicit formula and numerical inequalities have a separate derivation and interval replay. Seven here is an integer count. The $1/7$ in chapter 1 was the detector coefficient for an order-two character. [Fourier weight in Lean](lean/SuperZeta/GaussianDiskKernel.lean) · [Disk count in Lean](lean/SuperZeta/GaussianDiskCount.lean) · [Alpöge’s coefficient rule](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L37-L41)

</details>

<div><a name="research-impact"></a><a name="conclusions"></a><a name="read-consequences" id="user-content-read-consequences"></a><a name="zero-transport-questions"></a><a name="questions-in-the-order-i-asked-them"></a><a name="read-questions" id="user-content-read-questions"></a></div>

## Proofs, figures and open questions

The immediate question is whether cancellation in the omitted Gaussian terms preserves a gap in the phase around the entire right circle. If the full boundary stays nonzero and misses one spiral phase, its winding is zero. The argument principle would then clear the disk, and reflection would clear its partner. [Circle measurements](archive/2026-11-20-gaussian-circle-phases-v001/README.md) · [Earlier real-part test](docs/proofs/reciprocal-constructions.md#gaussian-disk-remainder)

<details>
<summary><strong>Global cancellation in the quartic field and two open questions about the tower</strong></summary>

For the quartic field I ask whether its smoothed prime-power sum $G_E(x)$, after subtracting the two specified main terms, satisfies $\lvert G_E(x)\rvert\le C_\epsilon x^{1/2+\epsilon}$ at every $x\ge2$ for every $\epsilon>0$. This would make its Mellin integral holomorphic for $\Re v>-1/2$, where a field zero $\rho$ with $\Re\rho>1/2$ would force a pole at $v=\rho-1$. Chapter 1 gives a finite, one-sided estimate for the Eisenstein field. [Main terms and pole calculation](archive/2026-11-20-dedekind-phase-v001/README.md#which-zero-counts-transfer)

Can the ordered stages supply the three character residues independently of reducing my quartic? And how do the certified finite Dottie orbits match the limiting horn maps? I keep the questions in the order I asked them, alongside the calculations that settled the earlier ones. [Research questions and results](docs/proofs/reciprocal-constructions.md#user-content-read-questions)

</details>

<div><a name="preprints-and-reproduction"></a><a name="read-preprints" id="user-content-read-preprints"></a></div>

<details>
<summary><strong>Proofs, interactive figures, preprints and reproduction by topic</strong></summary>

My two preprints give the definitions of the reciprocal tower and the Dottie fold. The full proof links each calculation to its source, including the two certified paired periods 640 and 205,440. [Preprints and replay commands](docs/proofs/reciprocal-constructions.md#user-content-read-preprints) · [Mixed-period certificate](archive/2026-11-18-dottie-mixed-cap-period-v001/README.md)

| Topic | Proof or data |
| --- | --- |
| Quadratic approximation, two ovals and the local/global obstruction | [Quartic derivation and descent](docs/proofs/reciprocal-constructions.md#user-content-read-quartic) |
| <a name="the-complex-two-base-family"></a><a name="read-sign-words" id="user-content-read-sign-words"></a>Distinct exponential sign words, consecutive stage products and primitive periods | [Sign recovery](docs/proofs/reciprocal-constructions.md#user-content-read-sign-words) · [Finite periods and the open horn correspondence](docs/proofs/reciprocal-constructions.md#user-content-read-dottie-spire) |
| <a name="the-boundary-operator-behind-the-determinant"></a><a name="34-the-boundary-operator-behind-the-determinant"></a>Cosine spectrum, Fredholm determinant and relative Mellin correction | [Operator proof](docs/proofs/quartet-spectrum.md) · [Reproduction guide](archive/2026-11-18-spectral-reproduction-v001/README.md) |
| <a name="read-period-640" id="user-content-read-period-640"></a><a name="oriented-period-640-return"></a><a name="36-inverting-two-spectral-traces-on-the-period-640-orbit"></a>Orientation of the period-640 return from two spectral measurements | [The signed angle and its interval inverse](archive/2026-11-19-oriented-return-v001/README.md) |
| <a name="zero-transport"></a><a name="37-following-a-zero-from-one-turn-to-the-next"></a><a name="38-why-the-sixth-path-folds-back"></a><a name="39-what-one-hurwitz-term-remembers-about-the-orbit"></a><a name="310-what-a-full-turn-changes-near-the-sixth-zero"></a>Paths of the symmetric Hurwitz zeros, intermediate crossings and the inverse from one summand | [Continuation between endpoints](archive/2026-11-19-zero-transport-v001/README.md) · [Three visits at the same height](archive/2026-11-19-sixth-passes-v001/README.md) · [One-term inverse](archive/2026-11-19-single-term-inverse-v001/README.md) |
| <a name="read-liu-speed" id="user-content-read-liu-speed"></a><a name="read-speed-moment" id="user-content-read-speed-moment"></a>Angular velocity at the two signed angles and its mean square at Riemann zeros | [Velocity and Liu’s bound](archive/2026-11-20-liu-angular-velocity-v002/README.md) · [Mean squared speeds](docs/proofs/reciprocal-constructions.md#user-content-read-speed-moment) |
| <a name="read-two-inputs" id="user-content-read-two-inputs"></a>Two independent spectral inputs and recovery of the first conjugate pair | [Two-input spectrum](docs/proofs/reciprocal-constructions.md#user-content-read-two-inputs) |
| <a name="the-factorial-correction"></a><a name="5-the-factorial-correction"></a><a name="read-factorial" id="user-content-read-factorial"></a><a name="what-the-quarter-measures"></a><a name="recovering-the-error-on-one-factorial"></a><a name="where-the-correction-enters-the-level-zeta"></a><a name="what-the-barnesdottie-constant-measures"></a>Central-binomial sign weighting, finite Hurwitz transition and the Barnes–Dottie limit | [Factorial and quartet proofs](docs/proofs/reciprocal-constructions.md#user-content-read-factorial) |
| Three distinct ideal classes at discriminant $-23$ and the non-Galois cubic comparison | [Class weights, units and coefficient checks](archive/2026-11-20-dedekind-phase-v001/README.md) |

</details>

<div><a name="credits"></a><a name="read-credits" id="user-content-read-credits"></a></div>

## Credits

I use Baker and Rippon’s iteration theory at the Dottie fold, McPhedran, Botten and Nicorovici’s symmetrized Hurwitz family for zero motion, and the zero-free bounds of OpenAI and Baiying Liu. The Gaussian prime angles use Rudnick and Waxman’s fourth angular harmonic, and the completed zero sum uses the Hecke framework described by Lemke Oliver and Thorner. The field calculations use quadratic factorization, ideal norms and quadratic Hecke characters. The formal and numerical checks use Lean, mathlib, FLINT and PARI/GP. [Rudnick and Waxman, §4.1](https://arxiv.org/pdf/1705.07498#page=13) · [Lemke Oliver and Thorner, §2](https://arxiv.org/pdf/1505.03122#page=10) · [Complete credits](docs/proofs/reciprocal-constructions.md#user-content-read-credits) · [Source map](archive/2026-11-16-super-zeta-v001/source-map.md) · [Archive and reproduction policy](PRESERVATION.md)
