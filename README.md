# The Super Zeta Function

<div><a name="abstract"></a><a name="introduction"></a></div>

I define the super zeta function from the fixed pairs of my reciprocal exponential tower. One update sends $(P,Q)$ to $(e^{LQ},e^{-LP})$. I keep the two exponents in order, $U=LQ$ and $V=-LP$. At a fixed pair, the derivative after two updates is $UV$ in either coordinate. I select the pairs with $UV=1$. Their difference $u=(U-V)/(2i)$ then satisfies $u=\cos u$ or $u=-\cos u$. Given $u$ and its sign in that equation, I can recover both exponents and the original parameter $L$. [Fixed pairs and their inverse, equations (1)–(3)](docs/proofs/quartet-spectrum.md#eq-1)

The two roots $u$ and $-u$ give one spectral value $v=u^2$. At unit coupling these values are exactly the zeros of the entire function $E$ below. I count them with multiplicity and use the principal logarithm for each inverse power. This is the defining sum, in the half-plane where it converges.

~~~math
E(v)=\cos^2\!\sqrt v-v,\qquad
\mathcal Z(s;1)=\sum_{E(v)=0}e^{-s\mathrm{Log}\,v},
\qquad \Re s>\tfrac12.
~~~

Ordinary zeta enters when I compare $E(v)$ with $\cos^2\!\sqrt v$. The reference has double zeros at the squares of the half-integer multiples $(n+\tfrac12)\pi$, for $n=0,1,\ldots$. Their inverse powers give the odd-integer part of the Riemann series. Integrating the logarithm of the determinant ratio on the negative real axis gives the correction $J$. After continuation their difference satisfies

~~~math
\mathcal Z(s;1)-J(s;1)=2\pi^{-2s}(2^{2s}-1)\zeta(2s).
~~~

Thus a Riemann zero at $w$ in the critical strip is a point where the continued super zeta and its correction agree at $s=w/2$, with the same order of vanishing for their difference. [Root sum, Mellin comparison and continuation](docs/proofs/quartet-spectrum.md#5-a-two-variable-zeta-for-the-inverse-cosine-coupling-family)

**Results in this proof**

- From the product for $E$ I obtain exact sums over the tower spectrum. For example, $\mathcal Z(1;1)=2$ and $\mathcal Z(2;1)=10/3$. [Determinant product and first four sums](docs/proofs/quartet-spectrum.md#4-canonical-product-and-exact-rational-trace-sums)
- Near the Dottie fold I isolate paired periods 640 and 205,440. A period-640 return sets three height windows in which all eleven Riemann zeros are simple and lie on the critical line, sharpening the 7/8ths and Liu bounds in those windows. [Orbit certificate](archive/2026-11-18-dottie-mixed-cap-period-v001/README.md) · [Three window counts](archive/2026-11-20-liu-angular-velocity-v002/README.md)
- From the balanced sign counts I recover the Stirling remainder for a single factorial. The actual quartet radii determine a finite Hurwitz sign change between levels 28 and 29. [Factorial proof](archive/2026-11-18-stirling-correction-v001/README.md) · [Comparison with equally spaced radii](archive/2026-11-18-quartet-grid-comparison-v001/README.md)
- I identify the arithmetic character of a branch of my quartic over the Gaussian integers. Its conductor gives three finite reductions that determine the sign at every nonzero marked Gaussian lattice point coprime to the conductor, and give zero at the excluded points. [Field and conductor proof](archive/2026-11-20-dedekind-phase-v001/README.md)
- I recover which branch supplied those signs from the completed zeros of an angular Hecke function. At norm 73 the two signs can then be read in order as exponential stages. Starting both words at 1 gives $\sqrt{2}$ and $1/4$. [Branch recovery and sign words](archive/2026-11-20-gaussian-branch-spectrum-v001/README.md)
- At any unknown nonzero integral lift $L=m\pi i$, two derivatives at the starting cap recover the magnitude of the lift and every signed exponential stage in order. One independently retained odd-stage prime reading also recovers which sign convention I used. [Theorem and blind experiment](archive/2026-11-20-hidden-lift-v001/README.md)

[Full derivations and preprints](docs/proofs/reciprocal-constructions.md) · [Interactive Hurwitz paths](https://nuckyducky.github.io/The-Super-Zeta-Function/) · [Two-input spectral map](https://nuckyducky.github.io/The-Super-Zeta-Function/two-input/)

The three arrows into the quartic field zeta are its three factors. The Gaussian factor uses both the discriminant from my quadratic and the lattice point marked in my ordered lift.

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

<div><a name="from-the-original-meme-to-the-dottie-spire"></a><a name="the-quadratic-and-the-genus-one-curve"></a><a name="1-the-quadratic-and-the-genus-one-curve"></a><a name="read-quartic" id="user-content-read-quartic"></a></div>

<details open>
<summary><h2>The quadratic, the ordered exponential stages and the spectrum</h2></summary>

My six coefficients define $N(x)=465x^2-183x-659$ and $D(x)=155x^2+396x-936$. Equating their ratio to $(1+y)(2+y)/(y^2+y-1)$ gives a quadratic in $y$. Set $A=N-D$ and $Y=2Ay+N-3D$. Completing the square gives

~~~math
Y^2=f(x)=A(x)^2+4N(x)^2
       =\bigl(A(x)+2iN(x)\bigr)\bigl(A(x)-2iN(x)\bigr).
~~~

<div><a name="what-the-right-panel-shows"></a><a name="real-ovals-and-projective-completion"></a><a name="the-point-giving-my-approximation-to-π"></a></div>

The signs of $Y$ give two real branches. Adding their points at infinity closes each into an oval. For the arithmetic in §2 I use the factor $A+2iN$. Its discriminant determines which Gaussian prime splits in the quartic field, even when two primes have the same norm. [Diagram of the ovals and the quartic derivation](docs/proofs/reciprocal-constructions.md#user-content-read-quartic)

<div><a name="reciprocal-tetration"></a><a name="2-reciprocal-tetration"></a><a name="read-tetration" id="user-content-read-tetration"></a></div>

For the reciprocal bases $e^L,e^{-L}$ I start both phases at $1$ and iterate $F_L(P,Q)=(e^{LQ},e^{-LP})$. At a fixed pair, $P=e^U$ and $Q=e^V$ with $U=LQ$ and $V=-LP$. Two updates return to the same coordinate. Their derivative at the fixed pair is $UV$. It reaches one at the Dottie fold. The colors below record the period reached from the same cap as I vary $L$. Gray means that the survey reached its iteration limit with no period in its search range. [My tetration preprint](archive/2026-11-18-lean-foundations-v001/papers/foundations/main.pdf) · [My Dottie spire preprint](archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.pdf) · [Figure and sampling limits](archive/2026-11-18-research-figures-v001/README.md)

<div><a name="the-dottie-spire"></a><a name="read-dottie-spire" id="user-content-read-dottie-spire"></a></div>

![Paired periods in the complex logarithm plane, with the neighborhood of the Dottie fold magnified on the right.](archive/2026-11-18-research-figures-v001/dottie-spire.png)

<div><a name="the-spectral-zeta-and-the-critical-line"></a><a name="building-the-super-zeta"></a><a name="3-building-the-super-zeta"></a><a name="read-super-zeta" id="user-content-read-super-zeta"></a></div>

**Which function am I studying?** Each row describes a different operation on the original return or its arithmetic reference.

| Input | Construction | Result |
| --- | --- | --- |
| <a name="1-compose-the-two-marked-stages"></a><a name="31-compose-the-two-marked-stages"></a><a name="2-recover-the-marked-phases-from-the-cosine-roots"></a><a name="32-recover-the-marked-phases-from-the-cosine-roots"></a><a name="3-square-the-roots-and-sum-their-inverse-powers"></a><a name="33-square-the-roots-and-sum-their-inverse-powers"></a>Fixed pairs with $UV=1$ | Put $U=\alpha$, $V=\alpha^{-1}$ and $2iu=\alpha-\alpha^{-1}$. The fixed equations give $u=\pm\cos u$. | The zeros $\lambda=u^2$ of the entire function $E(v)=\cos^2\sqrt v-v$ are the spectrum. The reciprocal-power sum $\mathcal Z(s;1)=\sum_\lambda\lambda^{-s}$ uses principal logarithms and initially converges for $\Re s>1/2$. [Proof](docs/proofs/quartet-spectrum.md) |
| <a name="4-compare-with-the-odd-integer-spectrum"></a><a name="35-compare-with-the-odd-integer-spectrum"></a>The determinant and the half-integer cosine spectrum | On the negative axis their ratio is $1+t/\cosh^2\sqrt t$. Its logarithm gives the Mellin correction $J$. | $\mathcal Z(s;1)-J(s;1)=2\pi^{-2s}(2^{2s}-1)\zeta(2s)$. In the open critical strip, a Riemann zero at $w$ has the same multiplicity at $s=w/2$ in the difference. [Mellin proof](docs/proofs/quartet-spectrum.md) |
| The symmetrized Hurwitz reference with an angle $a$ | The two shifts are $1/2-a/\pi$ and $1/2+a/\pi$. At $a=\pi/6$ the value adds the classes $1,2\bmod 3$. Its angular derivative subtracts them. | After removing the explicit prefactors and shifting the derivative input by one, these readings give $\zeta(w)$ and $L(w,\chi_{-3})$. Their product is a quadratic field zeta. [Angular formula and its domain](archive/2026-11-20-liu-angular-velocity-v002/README.md) |
| The two ordered logarithms at a fixed pair | Mark a vector by its two integers $m,n$ and measure the squared length of $m+nU/V$. | At $U/V=e^{2\pi i/3}$ this is the Eisenstein norm. At $U/V=i$ it is the Gaussian norm. The extra prime weight at the Gaussian ratio comes from $f$. [Lattice derivation](archive/2026-11-20-dedekind-phase-v001/README.md) |

The lattice ratios use fixed pairs of the full logarithmic lift. For example, the fixed pair at $u=\pi/4$ has multiplier $\pi^2/8$. The multiplier-one condition selects the smaller family in the first row. [Ordered phases and inverse logarithmic lift](lean/SuperZeta/DedekindLift.lean)

</details>

<details>
<summary><h2>1. Arithmetic weights from the two logarithms</h2></summary>

Write $\tau=U/V$ and $d=V-U$. Then $e^d=-\tau$. For every $\tau$ in the upper half-plane and every choice of $d$ with this exponential, I recover the two original exponents by $V=d/(1-\tau)$ and $U=\tau V$, and the original parameter by $L=Ue^{-V}$. Thus I can specify both the lattice shape and the logarithm sheet. [Lean proof against the ordered map](lean/SuperZeta/DedekindLift.lean)

At the native parameter $u=\pi/6$, $\tau=-e^{-2iu}=\omega=e^{2\pi i/3}$. The squared length of $m+n\omega$ is $m^2-mn+n^2$. Every nonzero ideal in the Eisenstein integers is principal. Multiplying a generator by one of the six units gives the same ideal six times in the lattice sum. Consequently, for $\Re w>1$,

~~~math
\frac16\sum_{(m,n)\ne(0,0)}(m^2-mn+n^2)^{-w}
=\zeta_{\mathbb Q(\sqrt{-3})}(w)=\zeta(w)L(w,\chi_{-3}).
~~~

For this field the coefficient of $\log p$ at $p^j$ in its negative logarithmic derivative is $1+\chi_{-3}(p)^j$. The earlier weighted detector used $1+\chi_{-3}(p)^j/7$. At $p=2$ the field weights for $2,4,8$ are $0,2,0$. The prime is inert, so its first ideal has norm $4$. With the field weights and the corresponding main terms, 160-bit interval arithmetic gives the one-sided bound $G_K(x)<0.065597\sqrt{x}$ at every real cutoff $6501\le x\le4194304$. Here $x$ measures how far the prime-power sum runs. [Exact definition, four overlapping ranges and replay](archive/2026-11-20-dedekind-phase-v001/README.md) · [Quadratic factorization, Aycock and Kobin](https://arxiv.org/abs/2205.06298)

</details>

<details>
<summary><h2>2. A phase hypothesis from my quartic</h2></summary>

At $u=\pi/4$ the ordered ratio is $i$. A Gaussian generator $z=m+ni$ now marks a point in the lattice supplied by the lift. The branch polynomial $A+2iN$ from the first equation has discriminant $\delta=-5045155+1027708i$. Its roots generate $E=\mathbb Q(i,\sqrt{\delta})$ over $k=\mathbb Q(i)$. I use $E$ here for the number field and $E(v)$ above for the spectral determinant. The normal closure of the branch field over $\mathbb Q$ has dihedral group of order eight. [Derivation from the six coefficients](archive/2026-11-20-dedekind-phase-v001/README.md)

**Hypothesis to test.** For an unramified Gaussian prime of odd rational prime norm, can I recover the splitting of my branch from its marked direction in the lift? Splitting means two primes above it in $E$, with sign $+1$. A prime that stays prime has sign $-1$. To make the question reproducible I take the angle modulo $\pi/2$ (unit multiples give the same ideal), keep the quartic coefficients fixed, and test the sign against direct factorization in the residue field.

**Answer for exact angles.** A split rational prime has a primitive Gaussian generator. Its exact direction in the first quadrant gives the reduced slope $n/m$, hence the two integers and the prime norm. Reducing $m+ni=0$ at that prime gives the image of $i$ as $-m/n$. This specifies which reduction of my quadratic to factor. For ideals of arbitrary norm I retain both integer coordinates. If I also bound the tested prime norms by $X$, an angular error smaller than $\tfrac12\arcsin(1/X)$ suffices to identify the marked split prime. A direction shared by $z$ and $73z$ gives opposite signs whenever both ideals are coprime to the conductor. [Direction proof and angular precision](docs/proofs/marked-gaussian-direction.md) · [Residue calculation in Lean](lean/SuperZeta/FieldWeights.lean)

</details>

<details>
<summary><h2>3. Phase tests at conjugate Gaussian primes</h2></summary>

The two points $3+8i$ and $3-8i$ both have squared length $73$. At the first, $i$ reduces to $27\bmod 73$ and the branch has no root. At the second, $i$ reduces to $46$ and the branch has two roots. The sign can therefore distinguish two primes that every function of the integer norm treats alike. At norms 13 and 37 the signs agree on the two sides.

| Norm | Marked generators in the order tested | Signs |
| ---: | --- | --- |
| 13 | $2+3i$, $2-3i$ | $-1,\ -1$ |
| 37 | $1+6i$, $1-6i$ | $+1,\ +1$ |
| 73 | $3+8i$, $3-8i$ | $-1,\ +1$ |

For every nonzero $z=m+ni$ the quadratic Hecke character $\eta_\delta((z))$ is given by the following three Legendre symbols, with value zero on ideals that share a prime with the conductor. The conductor is the ideal $(\delta)$. Each pair $(p,t)$ below is a prime divisor of its norm and the image of $i$ at the corresponding prime ideal. For example, $t=32$ satisfies both $t^2=-1\bmod41$ and $\delta=0\bmod41$ after substituting $i=t$.

~~~math
\eta_\delta((m+ni))=
\prod_{(p,t)\in\{(41,32),(457,109),(1414835497,516876951)\}}
\left(\frac{m+nt}{p}\right).
~~~

Multiplying the formula for $z$ by the one for its conjugate replaces each numerator by $m^2+n^2$ inside its Legendre symbol. Away from the conductor this tells me from the norm alone **whether the two signs agree**. Keeping the marked coordinates tells me **which prime gets which sign**. I can now compare any candidate reading of the ordered exponential stages against these values. Whether a spectral observable of the stages alone produces the character is open. [Conductor proof and direct prime checks](archive/2026-11-20-dedekind-phase-v001/README.md)

<details>
<summary><strong>Recovering the quartic branch from the completed zeros and reading its sign word</strong></summary>

Conjugating my quartic interchanges the primes above 73 and preserves the field zeta. To recover the branch I keep the positive imaginary direction fixed by $U/V=i$ and weight each marked ideal by the fourth power of its unit direction. The ordinary coefficient gives the sum of the two prime signs. The imaginary part of the angular coefficient gives their difference times a known sine. This recovers which prime received each sign.

The same choice is visible in the zeros of the completed angular function. Counting every zero $\rho$ with its multiplicity, the quantity $-\Im\sum_\rho(2-\rho)^{-2}$ is positive for $A+2iN$ and negative for $A-2iN$. I bounded it by evaluating the corresponding differentiated Euler series, including its infinite tail. Reading $3+8i$ before $3-8i$ then gives the sign words $-+$ and $+-$. Under the original exponential stages with $L=\log 2$ their respective cap values are $\sqrt{2}$ and $1/4$. [Proof and numerical enclosures](archive/2026-11-20-gaussian-branch-spectrum-v001/README.md) · [Lean proof of ordered recovery](lean/SuperZeta/MarkedBranch.lean)

Lean proves that relabeling the zeros preserves this sum and that conjugating them reverses its sign. Since the value at 2 excludes zero, the two completed angular functions have different complex zero multisets. The individual zero where they first differ is still unknown. [Lean proof of the zero sum and conjugation](lean/SuperZeta/ZeroMoment.lean)

</details>

<details>
<summary><strong>Lemma. Unique chronological order of the signed stages</strong></summary>

At a fixed positive real lift, two finite sign histories give the same endpoint from the cap $1$ exactly when the signs agree at every stage. Parentheses can move because composition is associative. The last sign can be read from the endpoint itself. If it lies above $1$, the last stage was plus. If it lies below $1$, the last stage was minus. Taking the absolute logarithm and dividing by the lift recovers the preceding value.

My earlier balanced-history count assigns the same weight to `++--`, `--++`, and `-+-+`. The first two even describe the same cyclic order when the starting phase is hidden. Applied from the same cap at base 2, the three words give $0.957603\ldots$, $3.100555\ldots$, and $1.297032\ldots$, respectively. At the complex lift $L=\pi i$, every nonempty word sends that same cap to $-1$. [Proof, six exact endpoints and the complex example](docs/proofs/chronological-order.md) · [Lean formalization](lean/SuperZeta/SignWords.lean)

</details>

<details>
<summary><strong>The second cap derivative recovers the sign order at the common endpoint</strong></summary>

I keep $L=\pi i$ fixed and vary the starting value $z$ in the same signed exponential stages. All six balanced four-stage words give $W(1)=-1$ and $W'(1)=\pi^4$. They leave that point with the same velocity for a real change in the cap. Their complex accelerations $W''(1)$ distinguish all six. For example, the words `++--` and `+-+-` bend upwards at the same rate there, but their horizontal accelerations differ.

For any finite sign word, let $c_j$ be the product of its first $j$ signs. The chain rule gives

~~~math
\frac{W''(1)}{W'(1)}=-\sum_{j=1}^{n}c_j(-\pi i)^j.
~~~

The highest power at which two histories differ outweighs every lower difference combined. This makes their derivative ratios distinct even when their lengths are hidden. To compare with the earlier prime detector, I use one exponent step for each minus and two for each plus. At powers of 2 the detector then records $1+c_j/7$, while the quadratic field records $1+c_j$. Both readings recover the same signs in order. [Derivation and blind test](archive/2026-11-20-cap-derivative-recovery-v001/README.md) · [Lean proof for all finite words](lean/SuperZeta/CapRecovery/Dominance.lean) · [General detector weights](lean/SuperZeta/CapRecovery/GeneralWeights.lean)

</details>

<details>
<summary><strong>Recovering an unknown integral lift and an ordered sign word</strong></summary>

Within this family I can decide whether two compositions agree for every complex starting value by comparing just their first two derivatives at 1. This includes the empty word, which acts as the identity, and the nonempty words at zero lift, which are constant.

When I hide both the word and the integer in $L=m\pi i$, the stage rates still have a unique reconstruction. For a nonempty word and $m\ne0$, I measure $K=W''(1)/W'(1)$. If both Cartesian components are nonzero, dividing the larger absolute component by the smaller gives $|m|\pi$ to within one unit. Rounding after division by $\pi$ gives $|m|$. A single stage gives $|K|=|m|\pi$ exactly. With the positive lift as representative I can now recover the word, including its length.

The two labels $(2,\text{+--})$ and $(-2,\text{-++})$ give the same exponential at every stage. To recover the original labels, I retain the prime reading at the first selected power of two. With the earlier weight $1/7$ it reads $8/7$ for the first label and $6/7$ for the second. This is where the arithmetic supplies information the two derivatives cannot distinguish. [Proof, calculation and replay](archive/2026-11-20-hidden-lift-v001/README.md) · [Lean statement](lean/SuperZeta/CapRecovery/HiddenLift.lean)

</details>

</details>

<div><a name="4-strengthening-the-78ths-and-liu-bounds-in-three-height-intervals"></a><a name="a-local-strengthening-of-the-seven-eighths-theorem"></a><a name="local-zeta-result"></a><a name="a-local-strengthening-of-the-78ths-theorem"></a><a name="4-a-local-strengthening-of-the-78ths-theorem"></a><a name="read-zero-counts" id="user-content-read-zero-counts"></a></div>

<details>
<summary><h2>4. Transferring zero results one factor at a time</h2></summary>

The first field involves ordinary Dirichlet characters. The quartic adds a character of ideals over the Gaussian integers. Write $\beta_D(w)=L(w,\chi_{-4})$ for Dirichlet beta. The three factorizations specify which extra function has to be evaluated when I carry a zero count into a new field.

~~~math
\begin{aligned}
\zeta_{\mathbb Q(\sqrt{-3})}(w)&=\zeta(w)L(w,\chi_{-3}),\\
\zeta_k(w)&=\zeta(w)\beta_D(w),\\
\zeta_E(w)&=\zeta(w)\beta_D(w)L_k(w,\eta_\delta).
\end{aligned}
~~~

Dirichlet beta can also be read from the same symmetrized Hurwitz function $R(a,v)=\pi^{-v}[\zeta(v,b)+\zeta(v,1-b)]$, with $b=1/2-a/\pi$. Differentiate in $a$ and evaluate at $v=w-1$. At $a=\pi/4$, subtracting the two Hurwitz sums weights the classes $1,3\bmod 4$ with opposite signs, giving $\partial_a R(\pi/4,w-1)=(w-1)(4/\pi)^w\beta_D(w)$. The angle $\pi/6$ gives $L(w,\chi_{-3})$ by the same calculation with modulus three. [The prime weights and both evaluations](archive/2026-11-20-dedekind-phase-v001/README.md) · [Check against Dirichlet values](archive/2026-11-20-dedekind-phase-v001/first-zero.md)

<div><a name="how-the-iteration-gives-the-height"></a><a name="selection-of-the-test-height"></a><a name="what-the-three-windows-tell-me"></a><a name="certified-counts-in-the-three-windows"></a></div>

A marked period-640 return first supplied a Riemann height $T_D\approx4.5261\times10^{12}$. I counted zeros in three windows centered at $T_D$, $2T_D$ and $3T_D$. The counts with multiplicity were 2, 5 and 4, each exhausted by disjoint critical-line sign changes. [Height selection from the ordered stages](archive/2026-11-17-dottie-grid-match-v001/README.md) · [Three full-strip counts](archive/2026-11-20-liu-angular-velocity-v002/README.md)

In the open critical strip all these factors are holomorphic. The order at any point is the sum of the orders of the factors. Thus each of the eleven certified Riemann zeros contributes at least one zero to each field product. To claim that a whole box has only those zeros, I need counts for every extra factor on the same contour. A *simple zero* means multiplicity one, equivalently that the first derivative there is nonzero. [Three Riemann counting intervals](archive/2026-11-20-liu-angular-velocity-v002/README.md) · [Field factors and the domain of Liu’s bound](archive/2026-11-20-dedekind-phase-v001/README.md)

Liu’s stated unitary Hecke bound applies directly to the finite-order character over $k$. Sutherland’s November 20 report records independent verification of the Riemann and Dirichlet statements in Alpöge’s submission. The latter includes Dirichlet beta. Taking those critical-line conclusions, the off-line zeros of my quartic field inside the critical strip are exactly those of its Gaussian Hecke factor, with the same multiplicity. [Sutherland’s verification report](https://math.mit.edu/~drew/grh/) A critical-line bound for the extra Gaussian-ideal factor would extend that conclusion to this particular quartic field. [Liu, Theorem 1.1](https://hexagonmath.org/pdf/2611.00421v1#page=2) · [OpenAI, Theorem 1.1](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf)

Masullo’s November 20 draft treats Hecke characters over number fields and gives a trace formula with a separate calculation for each character. For my quartic the relevant character is $\eta_\delta$ over $\mathbb Q(i)$. At norm 73 its two prime contributions cancel. Keeping the fourth angular harmonic gives a nonzero imaginary coefficient whose sign identifies the branch. [Calculation at 73 and reading guide to Masullo’s draft](docs/number-fields/masullo-trace-formula.md)

**Global hypothesis for my quartic field.** Let $G_E(x)$ be its smoothed prime-power sum after removing the two main terms specified in the proof. I ask whether for every $\epsilon>0$ some $C_\epsilon$ satisfies $\lvert G_E(x)\rvert\le C_\epsilon x^{1/2+\epsilon}$ for every real $x\ge2$. This two-sided bound would make its Mellin integral holomorphic for $\Re v>-1/2$. A field zero $\rho$ with $\Re\rho>1/2$ would give a pole at $v=\rho-1$ there. The field functional equation reflects the resulting exclusion across the critical line. The finite one-sided calculation in §1 uses the Eisenstein field. [Two main terms, pole residue and Mellin proof](archive/2026-11-20-dedekind-phase-v001/README.md#which-zero-counts-transfer)

**One reproduced transfer.** At the first positive Riemann zero I enclose the derivative of zeta and both additional Dirichlet values at the same complex point. All three enclosures exclude zero, so the zero has multiplicity exactly one in both quadratic field zetas. For the quartic field, its multiplicity is one plus the order of its Gaussian Hecke factor there. [160-bit calculation and replay](archive/2026-11-20-dedekind-phase-v001/first-zero.md)

<details>
<summary><strong>Two inverse branches of the Gaussian factor at the Dottie height</strong></summary>

In my quartic, two solutions of $P(z)=v$ meet and separate in a perpendicular direction as the real target $v$ passes a critical value. To test for the same event in the quartic field, I use its completed Gaussian factor $f$ and count the solutions of $f(w)=v$ in a fixed rectangle. When there are two, the contour gives their signed squared separation $(w_1-w_2)^2$. A change from positive to negative takes a same-height pair through a double solution on the critical line.

At $T_D$, directed arithmetic gives exactly two simple solutions for every real target with $1.05238\times10^{-18}\leq |v|\leq 6\times10^{-16}$. One lies to the right of $1.018$ and its partner to the left of $-0.018$, at the same height. As I reduce the magnitude of either signed target, the two move horizontally toward each other. The Gaussian zero count concerns the remaining target $v=0$, where the contour is still unresolved. [Proof, positions and reproduction](archive/2026-11-20-gaussian-two-root-transition-v001/README.md)

</details>

</details>

<details>
<summary><h2>Proofs, figures and open questions</h2></summary>

<div><a name="research-impact"></a><a name="conclusions"></a><a name="read-consequences" id="user-content-read-consequences"></a></div>

I keep the derivations, figures, and computational certificates together so each assertion can be traced back to the equation or experiment that produced it.

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

<div><a name="zero-transport-questions"></a><a name="questions-in-the-order-i-asked-them"></a><a name="read-questions" id="user-content-read-questions"></a></div>

The open field question is whether the native determinant, or another specified spectral reading of the ordered return, gives the three character residues independently of reducing the quartic. The test must specify the observable and its input before evaluating the comparison primes. The open spire question is how the certified finite cap orbits match to the limiting horn maps. [Chronological research questions](docs/proofs/reciprocal-constructions.md#user-content-read-questions)

<div><a name="preprints-and-reproduction"></a><a name="read-preprints" id="user-content-read-preprints"></a></div>

My two preprints give the definitions of the reciprocal tower and the local Dottie fold. Their TeX sources, PDFs and the commands to replay the archived and Lean checks are collected together. [My preprints and replay commands](docs/proofs/reciprocal-constructions.md#user-content-read-preprints)

</details>

<details>
<summary><h2>Credits</h2></summary>

<div><a name="credits"></a><a name="read-credits" id="user-content-read-credits"></a></div>

For the Gaussian prime angles I use the fourth angular harmonic in Rudnick and Waxman. The order-one completion used in the zero sum is the standard Hecke case of the analytic framework described by Lemke Oliver and Thorner. [Rudnick and Waxman, §4.1](https://arxiv.org/pdf/1705.07498#page=13) · [Lemke Oliver and Thorner, §2](https://arxiv.org/pdf/1505.03122#page=10)

I use Baker and Rippon’s iteration theory at the Dottie fold, McPhedran, Botten and Nicorovici’s symmetrized Hurwitz family for the motion of its zeros, and the bounds of OpenAI and Baiying Liu when locating nontrivial zeros. The field calculations use classical quadratic factorization, ideal norms, and quadratic Hecke characters. The formal and numerical checks use Lean, mathlib, FLINT and PARI/GP. Author and theorem references are listed beside the corresponding derivations. [Complete credits](docs/proofs/reciprocal-constructions.md#user-content-read-credits) · [Source map](archive/2026-11-16-super-zeta-v001/source-map.md) · [Archive and reproduction policy](PRESERVATION.md)

</details>
