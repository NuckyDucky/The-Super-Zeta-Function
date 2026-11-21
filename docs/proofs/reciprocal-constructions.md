# The reciprocal construction, its spectrum and its certificates

[Return to the proof map and number-field results](../../README.md)

<div><a name="abstract"></a><a name="introduction"></a></div>

I started with a quadratic approximation to π built from six integers and the number $e$. Its two real branches close into the two ovals of a genus-one quartic. At $x=e$ the upper branch gives my approximation $\widehat\pi$. Comparing the roots led me to the reciprocal difference $z-1/z$. I met the same expression in the alternating tower with stages $P'=e^{LQ}$ and $Q'=e^{-LP}$. At the Dottie fold the derivative of the two-stage return equals one. Imposing that same condition on all complex fixed pairs gives the signed cosine equations $u=\pm\cos u$. I call the sum of inverse powers of its squared roots the **super zeta function**. [Fixed pairs in my tetration preprint](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L360-L402) · [The Dottie fold](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L145-L244)

**Principal results**

- In three height intervals selected from the Dottie return, I sharpen the 7/8ths and Liu bounds to $`\Re w=1/2`$. The intervals contain 2, 5 and 4 distinct Riemann zeros respectively, and each occurs with multiplicity one. [Locations, counts and controls](#user-content-read-zero-counts)
- I recover the exact Stirling remainder of each $n!$ from the factorial weight on my quartet radii. Those radii give a Hurwitz sign change between levels 28 and 29. [Factorial correction](#user-content-read-factorial)
- The cosine roots of my reciprocal tower give a spectral determinant. Comparing it with the half-integer cosine spectrum recovers $\zeta(2s)$. [Determinant and proof](../../docs/proofs/quartet-spectrum.md)
- Five high-precision readings at real parts 16 and 17 recover the modulus and angle of the first nonreal squared pair. [Two-input inverse and precision test](#user-content-read-two-inputs)
- Near the Dottie fold I isolate a paired orbit of period 205,440. On a period-640 orbit two ordered spectral measurements recover the parameter and its marked return. [Finite periods](#user-content-read-dottie-spire) · [Two-trace inverse](../../archive/2026-11-19-oriented-return-v001/README.md#the-two-trace-inverse)
- At $+\pi/6$ and $-\pi/6$ the Hurwitz zero paths have opposite velocities. I bound their normalized speed using Liu’s theorem, compute its mean square in the three intervals, and derive the long-run mean of the arithmetic quotient. [Angular velocity](#user-content-read-liu-speed) · [Mean squared speed](#user-content-read-speed-moment)
- Each finite sign order gives a distinct exponential map at every nonzero complex lift. Consecutive derivative products recover all 640 signed stages at the secondary centerline minimum. [Sign order and recovery](#user-content-read-sign-words)

**Contents**

[1. My quadratic and its two ovals](#user-content-read-quartic) · [2. Reciprocal tetration and the spire](#user-content-read-tetration) · [3. The super zeta](#user-content-read-super-zeta) · [4. Riemann zero counts](#user-content-read-zero-counts) · [5. The factorial correction](#user-content-read-factorial)

[The determinant proof](../../docs/proofs/quartet-spectrum.md) · [The two-input inverse](#user-content-read-two-inputs) · [The period-640 return](#user-content-read-period-640) · [Consequences](#user-content-read-consequences) · [Preprints and reproduction](#user-content-read-preprints) · [Open questions](#user-content-read-questions) · [Credits](#user-content-read-credits)

**Interactive figures** · [Follow three passes of the sixth-zero path at one height](https://nuckyducky.github.io/The-Super-Zeta-Function/) · [Vary both imaginary inputs of the quartet spectrum](https://nuckyducky.github.io/The-Super-Zeta-Function/two-input/)

<div><a name="from-the-original-meme-to-the-dottie-spire"></a><a name="the-quadratic-and-the-genus-one-curve"></a><a name="1-the-quadratic-and-the-genus-one-curve"></a></div>

<div><a name="read-quartic" id="user-content-read-quartic"></a></div>

## 1. The quadratic approximation to π and its genus-one quartic

I chose two integer quadratics $N,D$ so that their ratio at $x=e$ comes close to $T(\pi)$, where $T(y)=(1+y)(2+y)/(y^2+y-1)$. Solving $T(y)=N(x)/D(x)$ gives two values of $y$. Those two roots trace the two real ovals of a genus-one quartic. At $x=e$ the upper root gives my approximation $\widehat\pi$.

$`\displaystyle \begin{aligned} N(x)&=465x^2-183x-659,\\ D(x)&=155x^2+396x-936. \end{aligned}`$

Clearing the denominators gave me a quadratic in $y$. Completing the square gave me a new ordinate $Y$ and the equation $Y^2=f(x)$. In these formulas $N$ and $D$ are evaluated at $x$. [Quartic derivation, §1](../../archive/2026-11-18-lean-foundations-v001/arithmetic/research/geometry.md#1-the-exact-quadratic-and-the-quartic) · [Completing the square in Lean](../../lean/SuperZeta/Meme.lean)

$`\displaystyle \begin{aligned} 0&=(N-D)y^2+(N-3D)y-N-2D,\\ Y&=2(N-D)y+N-3D,\\ f(x)&=(N-D)^2+4N^2\\ &=961000x^4-1039740x^3-1810543x^2+644010x+1813853. \end{aligned}`$

[![The two signs of Y form separate real ovals. The marked upper point at x=e gives pi-hat.](../figures/proof-quartic-ovals.png)](../figures/proof-quartic-ovals.png)

<a name="fig-1"></a>**Fig. 1. The two real ovals of the quartic.** I plot $Y=\pm\sqrt{f(x)}$ at left, dividing each ordinate by $\sqrt{961000}(1+x^2)$ so both branches fit on the same axes. Blue is the positive branch and ochre the negative. On the right I follow each branch through its own hollow point at $x=\infty$, where its two ends join to complete one oval. Magenta marks the same point at $x=e$ in both panels. [Coordinates used in the drawing](../../archive/2026-11-18-quartic-ovals-v001/README.md)

<div><a name="what-the-right-panel-shows"></a><a name="real-ovals-and-projective-completion"></a></div>

### Real ovals and projective completion

Each real branch closes through its own point at infinity.

<details>
<summary>The points at infinity, genus and rational obstruction</summary>

To see why they stay apart, write $N-D=310(x-579/620)^2+8239/1240$. This is positive for every real $x$, so $f(x)=(N-D)^2+4N^2$ is positive too. The left figure plots the two heights $Y/[\sqrt{961000}(1+x^2)]$. The right figure uses $2\arctan x$ as the angle to bring the two ends of each graph together. [Plot coordinates and source](../../archive/2026-11-18-quartic-ovals-v001/README.md)

In the chart $t=1/x$, $V=Y/x^2$, the two points at $t=0$ satisfy $V^2=961000$. Both ends of the positive graph reach $V=310\sqrt{10}$, and both ends of the negative graph reach $V=-310\sqrt{10}$. The hollow dots mark those two points. Each graph closes into a circle through its own point at infinity. [Proof of the two real circles, §2](../../archive/2026-11-18-lean-foundations-v001/arithmetic/research/geometry.md#2-why-the-real-completion-is-exactly-two-circles) · [Radial drawing convention](../../archive/2026-11-18-quartic-ovals-v001/README.md)

Over $\mathbb C$ the degree-two projection to $x$ branches at the four simple roots of $f$. At each such root $x_0$, $f(x_0)=0$ and $f'(x_0)\ne0$. Riemann–Hurwitz gives $2g-2=2(-2)+4=0$, so the smooth completion has genus one and its complex points form a torus. I use the elliptic Jacobian to study rational points. [Complex genus, §3](../../archive/2026-11-18-lean-foundations-v001/arithmetic/research/geometry.md#3-why-the-complex-completion-is-a-torus) · [Explicit elliptic Jacobian, §5](../../archive/2026-11-18-lean-foundations-v001/arithmetic/research/geometry.md#5-an-explicit-elliptic-jacobian-and-its-complex-structure) · [Fisher, binary quartics, §2](https://people.maths.bris.ac.uk/~jb12407/ANTS-XV/papers/ANTS-XV_fisher.pdf)

The polynomial equation also gives the fibers where the quotient coordinates have poles. At $D=0$ the two roots satisfy $y^2+y-1=0$. At the complex points with $N-D=0$, the equation in homogeneous $y$ has the roots $y=-3/2$ and $y=\infty$. In the $t$-chart, the points with $x=\infty$ have $y=\pm\sqrt{5/2}$. [Quadratic coefficients and projective charts, §§1–2](../../archive/2026-11-18-lean-foundations-v001/arithmetic/research/geometry.md#1-the-exact-quadratic-and-the-quartic)

I call the input of the widest gap in the normalized plot Nucky’s constant, $x=0.057793510152240105777\ldots$. The stationary equation is $(1+x^2)f'(x)-4xf(x)=0$, and the narrowest gap is near $x=1.400168$. In the original $y$ coordinate the gap is $\sqrt{1+(2N/(N-D))^2}\ge 1$. Equality holds at both zeros of $N$, where the two roots are $-1$ and $-2$. [Stationary quartic and 384-bit enclosures](../../archive/2026-11-18-quartic-ovals-v001/README.md#where-the-branches-are-farthest-apart-and-closest-together) · [Exact gap in Lean](../../lean/SuperZeta/Meme.lean)

My quartic has points over $\mathbb R$ and every $\mathbb Q_p$, while its rational point set is empty. To find a local point I need only four rational inputs. For each prime $p$, at least one of $51/26$, $9/5$, $2/3$ and $2$ gives a value of $f(x)$ that is a square in $\mathbb Q_p$. A rational point would give a Jacobian point whose first coordinate is a nonzero negative square. The computer-assisted 2-isogeny descent excludes the squareclass $[-1]$. This gives a counterexample to the Hasse principle. [Local points in Lean](../../lean/SuperZeta/HasseCover.lean) · [Map and descent, eqs. (4)–(6)](../../archive/2026-11-18-lean-foundations-v001/arithmetic/research/hasse-obstruction.md#proof)

</details>

<div><a name="the-point-giving-my-approximation-to-π"></a></div>

### The upper root giving my approximation to π

My approximation to $\pi$ is the larger root of the original quadratic at $x=e$.

![The intersection yielding pi-hat lies about 8.682 times 10 to the minus 20 below pi](../figures/proof-pi-hat.png)

<a name="fig-2"></a>**Fig. 2. The quadratic root near π.** I center both axes at $(\pi,T(\pi))$ and magnify displacements by $10^{20}$. The blue curve gives $T(y)$ relative to $T(\pi)$, and the rust dashed line gives the corresponding level for $N(e)/D(e)$. Their intersection lies to the left of zero on the horizontal axis by about $8.6820$ units, giving $\pi-\widehat\pi\approx8.682007272725\times10^{-20}$. [Lean proof of the error bound](../../lean/SuperZeta/MemePrecision.lean)

<details>
<summary>Inverting the change of ordinate at x = e</summary>

I read $Y=+\sqrt{f(e)}$ on the upper oval, subtract $N(e)-3D(e)$, and divide by $2(N(e)-D(e))$. This reverses the change of ordinate and gives the following value. [Inverse coordinate and the two branches, §2](../../archive/2026-11-18-lean-foundations-v001/arithmetic/research/geometry.md#2-why-the-real-completion-is-exactly-two-circles) · [Upper-root identity in Lean](../../lean/SuperZeta/Meme.lean)

$`\displaystyle \widehat\pi=\frac{3D(e)-N(e)+\sqrt{f(e)}}{2\bigl(N(e)-D(e)\bigr)} =3.14159265358979323837582331055\ldots`$

I shift the ordinate to $p=2y+3$ to write the quadratic as $p-p^{-1}=4N/(N-D)$. The substitution $p\mapsto-1/p$ exchanges the two roots. On the exceptional fiber $N-D=0$, the same involution exchanges $p=0$ and $p=\infty$. [Reciprocal substitution in Lean](../../lean/SuperZeta/Meme.lean) · [Involutions of the quartic, §6](../../archive/2026-11-18-lean-foundations-v001/arithmetic/research/geometry.md#6-two-exact-involutions)

</details>

<div><a name="reciprocal-tetration"></a><a name="2-reciprocal-tetration"></a></div>

<div><a name="read-tetration" id="user-content-read-tetration"></a></div>

## 2. Reciprocal tetration in the logarithmic lift

I build a finite tower from its top value, the **cap** $T_0=1$. For a fixed logarithm $L$ of the base $x$, one stage sends $z$ to $e^{Lz}$, so $T_{n+1}=e^{LT_n}$ starts with $x$ and then $x^x$. I get reciprocal tetration by alternating the bases $x=e^L$ and $x^{-1}=e^{-L}$ and keeping track of which phase receives each exponent. For positive real $x$ I take $L=\log x$. For a complex base, choosing $L+2\pi i k$ can change the next stage even though the base is the same. [*Reciprocal Tetration*, §2, “Finite Tet and the reciprocal pair”](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L109-L146) · [PDF](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.pdf)

In my original pair $x^{x-a},x^{x+a}$, the two exponents are equally far from $x$. In the tower, the two current phases supply the exponents $Q$ and $-P$. Starting from $(P,Q)=(1,1)$, I apply the ordered update

$`\displaystyle F_L(P,Q)=\bigl(e^{LQ},e^{-LP}\bigr).`$

Their mean is $m=(Q-P)/2$ and their half-difference is $a=(Q+P)/2$. Thus $Q=m+a$ and $-P=m-a$, giving the next pair $(x^{m+a},x^{m-a})$. I retain the ordered exponents $U=LQ$ and $V=-LP$. My preprints write $M$ for the second phase $Q$. [*Reciprocal Tetration*, §5, “Branch-sensitive complex fixed data”](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L359-L402) · [Ordered return in Lean](../../lean/SuperZeta/Reciprocal.lean)

[![Paired periods reached from the cap across the complex logarithm plane, with a magnified view of the Dottie fold.](../figures/proof-dottie-spire.png)](../figures/proof-dottie-spire.png)

<a name="fig-3"></a>**Fig. 3. Paired periods near the Dottie fold.** At each complex logarithm $L$ I iterate from $(1,1)$, using four color samples per pixel. Blue identifies a fixed pair. The other period colors distinguish returns after 2 through 256 updates. The right panel enlarges the white rectangle around the fold $L_*$ (white dot), where neighboring parameters can give different return periods. Gray marks no period detected in 8,000 updates, dark navy an arithmetic limit, and purple a phase-precision limit. [Layer 4 survey and color key](../../archive/2026-11-18-research-figures-v001/README.md#the-dottie-spire) · [Derivation of the fold](#user-content-read-dottie-spire)

<div><a name="the-complex-two-base-family"></a></div>

### The complex two-base family

Two paired updates take each input back to its original coordinate. The first input passes through the minus stage and then the plus stage. The second passes through them in the opposite order.

<details>
<summary>The two scalar returns and their periods</summary>

I call each two-stage composition a **scalar return**. Squaring the paired map therefore separates the two coordinates.

$`\displaystyle F_L^2(P,Q)=\bigl(g_L(P),g_{-L}(Q)\bigr), \qquad g_L(z)=\exp\!\bigl(L\exp(-Lz)\bigr).`$

If the second base is $x^c=e^{cL}$, the first scalar return is $g_{L,c}(z)=\exp(L\exp(cLz))$. The equal-base tower has $c=1$ and the reciprocal tower has $c=-1$. For $L,c\ne0$ choose logarithms $\kappa$ and $\ell$ with $e^\kappa=L$ and $e^\ell=c$. The affine coordinate $z\mapsto\kappa+cLz$ conjugates this return to $E_\kappa\circ E_{\kappa+\ell}$, with $E_b(z)=e^z+b$. At $L=0$ the scalar return is constant $1$, and at $c=0$ it is constant $e^L$. [*Reciprocal Tetration*, §4, “Two-step scalar reduction and marked values”](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L242-L326) · [Baker and Rippon, Theorem 8.1](https://doi.org/10.1080/17476938908814364) · [Rempe and Schleicher, exponential parameter space](https://doi.org/10.1017/CBO9780511735233.014)

A primitive scalar period $r$ takes $2r$ exponential stages along one phase. An ordered periodic point solves $F_L^p(P,Q)=(P,Q)$, and its primitive paired period is the least positive $p$ for which both coordinates return. In the spire I follow the orbit approached from the cap. In each coordinate the even subsequence follows the corresponding scalar map from $1$. The odd updates in the first coordinate come from the other seed since $P_{2n}=g_L^n(1)$ and $P_{2n+1}=g_L^{n+1}(0)$. [*Reciprocal Tetration*, §4, marked values and symmetry](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L298-L341)

</details>

<div><a name="read-sign-words" id="user-content-read-sign-words"></a></div>

### Chronological sign words and recovery of the signed stages

At base 2 the six balanced four-stage histories give six different values from the same starting cap. At a particular complex lift all six endpoint values coincide. [Lemma on unique chronological order](chronological-order.md)

![A seven-stage sign word and its reversal, with a third panel marking changes in their measured periods at the same complex lift.](../figures/proof-reversal.png)

<a name="fig-4"></a>**Fig. 4. The effect of reversing seven exponential stages.** I sampled the same logarithms and starting cap in both period maps. The left panel uses $++-+---$, and the middle uses $++---+-$, a cyclic representative of its reversal. Red in the right panel marks the 14.8% of sampled inputs where the tuple-period classifications differ. These plot interiors preserve the preprint’s original measurements. [Sign-word survey, settings and precision replay](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L433-L453)

<details>
<summary>Recovering signs from endpoints and stage derivatives</summary>

The order of the signs can change the value reached from the same cap. At $L=\log 2$, the minus stage followed by the plus stage sends $1$ to $1/2$ to $\sqrt2$. Reversing them sends $1$ to $2$ to $1/4$. I write the signs in the order they act, so $-+$ denotes $E_+\circ E_-$ for $E_\pm(z)=e^{\pm Lz}$. These are the two scalar returns followed by $P$ and $Q$, respectively.

For **every fixed nonzero complex lift** $L$, two finite words give the same entire function exactly when every sign agrees in order. Moving the marked start around a periodic orbit rotates its word. If that changes the letter sequence, it changes the entire function. For real $L>0$ there is a shorter test from the cap $1$. The last sign is plus if the endpoint $x>1$ and minus if $0<x<1$. The previous value is $|\log x|/L$, so I can read the whole word backward. At the complex lift $L=\pi i$, both one-letter words send $1$ to $-1$, even though their entire functions differ. [My original definitions of rotation, reversal and complement](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L404-L445) · [Proof and all six balanced four-stage outcomes at the spire](../../archive/2026-11-19-ordered-signs-v001/README.md#the-order-of-the-signed-exponentials)

The complex orbit has a second way to read its signs. Write $C_j$ for the derivative of the first $j$ stages at their common starting point and put $d_j=C_j/C_{j-1}$. On an alternating return the output of stage $j+1$ is $e^{-d_j}$ and its signed rate is $d_{j+1}e^{d_j}$. At the secondary minimum the paired orbit first returns after 640 updates. I measure the first 160 and the first 161 stages from the same phase. Dividing the longer product by the shorter cancels their 160 common factors. I move the start forward **one stage** and repeat. Two successive ratios give one signed rate and its output. Sliding around the entire orbit recovers all 640 stage signs. The sign changes at each stage and repeats after two stages. The ordered state first repeats after 640 updates. [Derivation and measurements](../../archive/2026-11-19-ordered-signs-v001/README.md#recovering-one-alternating-stage-from-derivative-measurements) · [Lean proofs](../../lean/SuperZeta/SignWords.lean)

</details>

### Fixed pairs and their logarithms

At a fixed pair I can recover the logarithmic lift $L$ from the exponents used by the two stages.

<details>
<summary>The fixed-pair equation and its logarithmic sheets</summary>

Write $U=LQ$ and $V=-LP$. Since $P=e^U$ and $Q=e^V$, the two expressions for the lift are $L=Ue^{-V}=-Ve^{-U}$. Equating them gives $Ue^U+Ve^V=0$. Keeping $U$ and $V$ records the logarithms on their original sheets. At $L=0$ the pair is $(1,1)$ and both exponents vanish. [*Reciprocal Tetration*, §5](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L359-L402) · [Fixed-pair balance in Lean](../../lean/SuperZeta/Reciprocal.lean#L162-L197)

The difference $q=U-V$ gives one coordinate for the whole fixed-pair curve. The balance equation gives $V=-Ue^q$ and $q=U(1+e^q)$, so

$`\displaystyle U=\frac{q}{1+e^q},\qquad V=-\frac{qe^q}{1+e^q},\qquad L=\frac{q}{e^U+e^V}.`$

If $1+e^q=0$, the equation $q=U(1+e^q)$ would give $q=0$ at an odd multiple of $\pi i$. Thus the chart covers all finite fixed pairs with $`q\in\mathbb C\setminus\{(2k+1)\pi i:k\in\mathbb Z\}`$. For real $q$ the lift is strictly increasing and ranges over $\mathbb R$. On that real slice the cap converges to the unique positive fixed pair for every $L$, by the Baker–Rippon criterion. [*Reciprocal Tetration*, §3, real chart and convergence](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L147-L211) · [Global complex chart in q = 2iu](../../archive/2026-11-18-lean-foundations-v001/notes/monodromy.md#1-coordinates-and-constants)

</details>

<div><a name="the-dottie-spire"></a></div>

<div><a name="read-dottie-spire" id="user-content-read-dottie-spire"></a></div>

### The Dottie fold and the marked spire

The two centerline fixed branches meet at the Dottie number $d=\cos d$. Just above their meeting point, the same cap approaches cycles of different periods as I change the base.

<details>
<summary>The fold equation, period map and orbit certificates</summary>

I call this narrow stack of period groups the **Dottie spire**. On the centerline $L=iy$, both phases satisfy $Q=\bar P$, so I can follow the pair with Baker and Rippon’s half-step $H_y(z)=e^{iy\bar z}$. Its square is $g_{iy}$. On their fixed curve I put $q=2iu$ with $0<u<\pi/2$. [*Dottie Parabolic Fold*, §1, half-step and period conventions](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L100-L121) · [Baker and Rippon, eqs. (12)–(13)](https://doi.org/10.1080/17476938908814364)

$`\displaystyle \begin{aligned} L&=iY(u),&Y(u)&=u\sec u\,e^{-u\tan u},&Z(u)&=e^{u\tan u+iu},\\ g_{iY(u)}'(Z(u))&=(u\sec u)^2,\qquad& \frac{Y'(u)}{Y(u)}&=\frac{\cos^2u-u^2}{u\cos^2u}. \end{aligned}`$

At the maximum of $Y$ the derivative of the scalar return at its fixed point is one. The equation for that point is $d=\cos d$, where $d=0.7390851332\ldots$ is the Dottie number. The boundary is exactly $`L_{\ast}=ie^{-\sin d}\approx0.509863605523013\,i`$ and the fixed point is $Z_{\ast}=e^{\sin d+id}$. The quadratic term of $Y(d+h)-Y(d)$ is $-Y(d)(1+\sin d)h^2/d^2$, so the two fixed branches meet in a quadratic fold. I center and rescale the scalar return there to obtain the parabolic germ $f(z)=z+z^2+\cdots$. [*Dottie Parabolic Fold*, §2, exact fixed curve and fold](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L145-L243) · [§3, normalized germ and antiholomorphic square root](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L244-L304) · [Fold in Lean](../../lean/SuperZeta/Dottie.lean) · [Kaplan, *The Dottie Number*](https://doi.org/10.1080/0025570X.2007.11953455)

The Layer 4 survey tests paired periods through 256. For the longer cycles below I follow the orbit into a trapping disk and check its return and the shorter candidate periods with interval arithmetic. [Figure settings and orbit data](../../archive/2026-11-18-research-figures-v001/README.md) · [Finite-period certificates](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L554-L604) · [*Reciprocal Tetration*, §§6–8](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L404-L547)

I use the half-step in the normalized coordinates to obtain separate even and odd return equations. For an orbit of primitive paired period $p$ on the centerline, its period under $H_y^2$ is $p/\gcd(p,2)$. Thus paired periods 639, 640 and 641 have scalar periods 639, 320 and 641. In three finite parameter windows I certified that the cap enters a contracting disk and excluded every shorter period. [*Dottie Parabolic Fold*, §§5–6, cylinder and physical return equations](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L347-L489) · [§8, directed finite windows](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L554-L604) · [Window verifier](../../archive/2026-11-18-spectral-reproduction-v001/check_spire_windows.py) · [Rump, verified numerics](https://doi.org/10.1017/S096249291000005X)

At six lifts on the negative flank, the cap approaches a primitive scalar period-321 cycle in the first coordinate and a primitive period-320 cycle in the second. In the first coordinate the 320th scalar step makes a large excursion and the next lands near $1$. The return under $F_L^2$ takes $\mathrm{lcm}(321,320)=102720$ steps, so the orbit has primitive period **205,440** under $F_L$. Reflection $L\mapsto-\overline L$ gives the six corresponding lifts on the other flank and exchanges the coordinates after conjugation. [Proof, six inputs, and standalone verifier](../../archive/2026-11-18-dottie-mixed-cap-period-v001/README.md)

For the zeta experiment I use the two reflected lifts $L_\pm=\pm\eta+iy$ and their midpoint $L_0=iy$, with $\eta=4.749479070945369\times10^{-8}$ and $y=0.509892982511772$. At all three lifts I certify that under $F_L^2$ both coordinates approach scalar cycles of primitive period 320 from the cap, which gives primitive period 640 under $F_L$. These are the three marked orbits I use to select the height in §4. [Preprint §8, period-640 dynamics off the centerline](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L580-L604) · [Later three-point certificate, 384-bit arithmetic](../../archive/2026-11-18-lean-foundations-v001/checks/dottie_slice.py) · [Johansson, Arb ball arithmetic](https://arxiv.org/abs/1611.02831)

On the secondary centerline interval I continued the orbit selected by the cap through a second strict minimum of the return modulus, at $y\approx0.509893023733322309247$. Its 25 outside and 295 inside scalar phases retain the same gate order across the extension. The first minimum contracts by about $6.35\times10^{-17}$ per lap and the second by about $3.0154\times10^{-4}$. Both have primitive paired period 640. [Proof, detunings and independent interval check](../../archive/2026-11-19-ordered-signs-v001/README.md#two-minima-on-the-imaginary-centerline)

I can continue a marked period-640 cycle and its 25/295 itinerary across a finite centerline interval. The horn map passes between repelling and attracting Fatou coordinates at the fold. For the rail theorem I fix a nondegenerate local minimum of its multiplier. I assume that the relative Fatou normalization continues to that horn, that the cap itinerary and logarithmic branches persist, and that the minimum continues to a real detuning $\delta(E)=\delta_0+O(E)$ in the unfolding coordinate $E$. I also assume a solution $E_p=(2\pi/(p-\delta(E_p)))^2>0$ tending to zero for sufficiently large paired periods of the chosen parity. The heights $y_p$ on such a rail then obey

$`\displaystyle y_p-y_{\ast}=\frac{C_{\ast}}{(p-\delta_0)^2}+\frac{A_4}{(p-\delta_0)^4}+O(p^{-5}), \qquad y_{\ast}=e^{-\sin d},`$

where the coefficients $C_{\ast}$ and $A_4$ are explicit in $d$. My estimates of finite multiplier minima extend through paired period 4800. Carrying the entire cap approach and its logarithmic branches to a specific limiting horn in one common normalization is the remaining matching problem. [*Dottie Parabolic Fold*, §§9–10, rail law and finite data](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L605-L715) · [The finite orbit and the remaining horn matching](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L739-L750) · [Godin and Rousseau, antiholomorphic parabolic germs](https://doi.org/10.1017/etds.2021.98)

</details>

<div><a name="the-spectral-zeta-and-the-critical-line"></a><a name="building-the-super-zeta"></a><a name="3-building-the-super-zeta"></a></div>

<div><a name="read-super-zeta" id="user-content-read-super-zeta"></a></div>

## 3. The super zeta and the marked return

I obtain the super zeta by asking which fixed pairs have a two-stage return of derivative one. Their ordered exponents give $u=\pm\cos u$. Squaring each root gives a zero of $E(v)=\cos^2\sqrt v-v$. I define $\mathcal Z(s;1)$ by summing inverse powers of those squared roots. Their reciprocals sum to exactly 2. Comparing $E$ with $\cos^2\sqrt v$ gives the Mellin correction $J$ and the Riemann factor $\zeta(2s)$. [Recover the phases, eq. (3)](../../docs/proofs/quartet-spectrum.md#eq-3) · [Determinant, eq. (11)](../../docs/proofs/quartet-spectrum.md#eq-11) · [Reciprocal sum, eq. (18)](../../docs/proofs/quartet-spectrum.md#eq-18)

<div><a name="1-compose-the-two-marked-stages"></a><a name="31-compose-the-two-marked-stages"></a></div>

### 3.1 The multiplier of the two-step return

The multiplier is the derivative accumulated in one scalar return. At a fixed pair the stage from $P$ to $Q$ has derivative $-LQ$, and the stage back to $P$ has derivative $LP$.

<details>
<summary>The two derivatives in one return</summary>

Their product is $UV$ for the actual exponents $U=LQ$ and $V=-LP$. Thus the multiplier-one condition that defined the Dottie fold can be imposed on every complex fixed pair by setting $UV=1$.

$`\displaystyle g_L'(P)=(-LQ)(LP)=UV.`$

On the centerline curve this is $(u\sec u)^2$, and $Y'(u)/Y(u)=(1-UV)/u$. At the fold the multiplier is one, so a small displacement returns unchanged to first order. [*Reciprocal Tetration*, §5, fixed-pair identities](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.pdf#page=7) · [*Dottie Parabolic Fold*, §2, eqs. (6)–(9)](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.pdf#page=3)

</details>

<div><a name="2-recover-the-marked-phases-from-the-cosine-roots"></a><a name="32-recover-the-marked-phases-from-the-cosine-roots"></a></div>

### 3.2 Recovering the ordered fixed pair from a cosine root

A signed cosine root determines the ordered fixed pair at multiplier one.

<details>
<summary>Inverting the signed cosine equation</summary>

To derive the correspondence I put $U=\alpha$ and $V=\alpha^{-1}$ in the fixed-pair equation $Ue^U+Ve^V=0$. It gives $\alpha^2 e^{\alpha-\alpha^{-1}}=-1$. With $2iu=\alpha-\alpha^{-1}$ this reads $\alpha e^{iu}=\sigma i$ for a sign $\sigma=\pm1$, and substitution gives $u=\sigma\cos u$.

The calculation also runs backward. From a signed root I recover the ordered exponents, the parameter, and the fixed pair $(e^U,e^V)$.

$`\displaystyle U=\sigma\sin u+iu,\qquad V=\sigma\sin u-iu,\qquad L=\sigma i e^{-\sigma\sin u}.`$

[Cosine spectrum, §1, eqs. (1)–(5)](../../docs/proofs/quartet-spectrum.md#1-exact-recovery-of-every-ordered-phase-and-parameter) · [Phase recovery in Lean](../../lean/SuperZeta/Quartet.lean)

</details>

<div><a name="3-square-the-roots-and-sum-their-inverse-powers"></a><a name="33-square-the-roots-and-sum-their-inverse-powers"></a></div>

### 3.3 The squared cosine spectrum and its zeta function

The squared spectrum contains one positive real entry $d^2$ and a conjugate pair of entries from each nonreal quartet.

<details>
<summary>The spectral sum and its logarithm branch</summary>

The four roots $u_n,-u_n,\bar u_n,-\bar u_n$ give just $u_n^2$ and $\bar u_n^2$. I use $v=u^2$ because the even power series of $\cos^2 u$ then defines an entire determinant in $v$, with these entries as its zeros.

$`\displaystyle E(v)=\cos^2\sqrt v-v=1-2v+\frac{v^2}{3}-\frac{2v^3}{45}+\cdots.`$

I define the super zeta by summing inverse powers of the squared roots. For each root $\lambda$ I use $`\lambda^{-s}=\exp(-s\mathrm{Log}\,\lambda)`$, with the principal logarithm cut along the negative real axis.

$`\displaystyle \mathcal Z(s;1)=d^{-2s}+\sum_{n\ge1}\bigl[(u_n^2)^{-s}+(\bar u_n^2)^{-s}\bigr], \qquad \Re s>\frac12.`$

The squared roots $\lambda_j$ grow quadratically with the quartet index, so $\sum_j|\lambda_j|^{-1}$ converges. The determinant has order $1/2$, which leaves only a constant in front of its genus-zero Hadamard product. The normalization $E(0)=1$ fixes the constant. Differentiating the product gives the integer inverse-power sums, or **traces**, in the series near zero.

$`\displaystyle E(v)=\prod_j(1-v/\lambda_j),\qquad -\frac{E'(v)}{E(v)}=\sum_{m\ge1}\mathcal Z(m;1)v^{m-1}.`$

The first two traces are $\mathcal Z(1;1)=2$ and $\mathcal Z(2;1)=10/3$. The first ties the Dottie root to every nonreal quartet in one exact sum. Lean proves the product over the complete squared-root family. [Product, traces and a tail bound, eqs. (16)–(19)](../../docs/proofs/quartet-spectrum.md#4-canonical-product-and-exact-rational-trace-sums) · [Lean theorem](../../lean/SuperZeta/UnitSpectrum.lean)

There is an arithmetic pattern at every index. For a rational trace $S_m=\mathcal Z(m;1)$, I count the factors of two in its numerator minus those in its denominator. This equals the number of ones in the binary expansion of $m$. For instance, $S_3=92/15$ has two factors of two and $S_4=3538/315$ has one. The reference trace and the difference between the coupled and reference traces each have one fewer. [Coefficient proof and examples](../../archive/2026-11-18-binary-law-v001/README.md#what-the-binary-digits-measure) · [All-index proof in Lean](../../lean/SuperZeta/BinaryLaw.lean)

</details>

<div><a name="the-boundary-operator-behind-the-determinant"></a><a name="34-the-boundary-operator-behind-the-determinant"></a></div>

### 3.4 The midpoint boundary operator and its Fredholm determinant

The reciprocal fixed-pair equations determine the unit-coupling roots. To realize them as eigenvalues, I keep a function on $(-1,1)$ together with its midpoint value and take the average of its two endpoint values in the boundary operator. Varying the coupling in this operator gives a family of spectra that includes the original one.

<details>
<summary>Eigenvalue condition and determinant formula</summary>

More precisely the space is $L^2(-1,1)\oplus\mathbb C$. On the domain, $f$ has square-integrable weak derivative and the scalar coordinate satisfies $c=f(0)$. For complex coupling $\varepsilon\ne0$ my operator is

$`\displaystyle A_\varepsilon(f,c)=\left(-if',\frac{\varepsilon}{2}\bigl[f(-1)+f(1)\bigr]\right).`$

For eigenvalue $u$ the first coordinate gives $f(x)=c e^{iux}$, so the endpoint average in the second gives $u=\varepsilon\cos u$. The inverse $B_\varepsilon$ is Hilbert–Schmidt and its square is trace class. Its Fredholm determinant is the convergent determinant of $I-vB_\varepsilon^2$. At $\varepsilon=1$ it equals $E(v)$. [Operator, inverse and finite-matrix proof, eqs. (6)–(15)](../../docs/proofs/quartet-spectrum.md#2-a-boundary-operator-with-compact-inverse-and-the-cosine-spectrum)

$`\displaystyle \det(I-vB_\varepsilon^2)=\cos^2\sqrt v-v/\varepsilon^2.`$

The inverse sends scalar input $1$ to the constant function $1/\varepsilon$ in its first coordinate. Projecting onto normalized indicators of $N$ equal cells, with $N$ even, gives the scalar column

$`\displaystyle (B_N)_{j,N+1}=\frac{\sqrt{2/N}}{\varepsilon}.`$

For $N=2$, $\varepsilon=2$ and $u=1$, the projected determinant $\det(I-uB_N)$ is $1/8$. [Projection and determinant, eqs. (8), (12) and (13)](../../docs/proofs/quartet-spectrum.md#3-exact-fredholm-determinant-and-controlled-finite-matrices)

Hupkes’s midpoint condition gives the same characteristic equation in a continuous-history space. Put equal weights $i\varepsilon/2$ at the two endpoints and set $z=iu$ to get $i(u-\varepsilon\cos u)$. My starting point is the ordered reciprocal pair, which selects the unit-coupling spectrum and gives the Hilbert-space determinant used below. Varying $\varepsilon$ moves the roots. I can also add a shift $a$ to the squared roots, giving the series $\sum_j(\lambda_j+a)^{-s}$ with its own poles and residues. [Hupkes, eqs. (2.10), (2.54) and Lemma 2.4.4](https://math.leidenuniv.nl/scripties/PhdHupkes.pdf) · [Shifted spectrum, domain and residues](../../archive/2026-11-16-super-zeta-v001/research/shifted-superzeta.md)

</details>

<div><a name="4-compare-with-the-odd-integer-spectrum"></a><a name="35-compare-with-the-odd-integer-spectrum"></a></div>

### 3.5 The Mellin correction and the Riemann zeta factor

The Riemann factor comes from the reference determinant $\cos^2\sqrt v$. It has a double zero at each $[(n+1/2)\pi]^2$ for $n\ge0$.

<details>
<summary>Reference spectrum and Mellin integral</summary>

Summing their inverse powers gives the odd-integer part of $\zeta(2s)$ times $2(2/\pi)^{2s}$. To compare with my determinant I integrate along $v=-t$. There $E(-t)=\cosh^2\sqrt t+t>0$ for $t\ge0$, so I take the real logarithm starting at $\log E(0)=0$. The determinant integral agrees with the root sum for $1/2<\Re s<1$.

Dividing by the reference leaves $1+t/\cosh^2\sqrt t$. Its logarithm gives the Mellin correction after an integration by parts.

$`\displaystyle J(s;1)=\frac{s\sin(\pi s)}{\pi} \int_0^\infty t^{-s-1}\log\left(1+\frac{t}{\cosh^2\sqrt t}\right)\,dt \qquad (\Re s<1).`$

Subtracting Taylor terms at $t=0$ continues the integral. The factor $\sin(\pi s)$ cancels the poles from the subtracted terms, so $J$ is entire. This gives the meromorphic continuation of the super zeta and the corrected function

$`\displaystyle F(s)=\mathcal Z(s;1)-J(s;1)=2\pi^{-2s}(2^{2s}-1)\zeta(2s).`$

With $w=2s$, the prefactor is nonzero in $0<\Re w<1$. There $\zeta(w)=\pi^w F(w/2)/[2(2^w-1)]$, with the same zero multiplicities. In particular $w=1/2+iT$ corresponds to $s=1/4+iT/2$. Lean identifies the root sum with the continuation on the Mellin strip and proves the multiplicity identity on the pulled-back critical strip. [Cosine spectrum, §5, eqs. (20)–(23)](../../docs/proofs/quartet-spectrum.md#5-a-two-variable-zeta-for-the-inverse-cosine-coupling-family) · [Voros, zeta functions over zero sets](https://arxiv.org/abs/1403.4558) · [DLMF, Mellin transforms](https://dlmf.nist.gov/2.5) · [Lean determinant product and root sum](../../lean/SuperZeta/UnitSpectrum.lean)

</details>

I also tested how much information the individual quartet layers retain. If $d=\Delta X+i\Delta Y$ is a displacement in the $w$-plane, the outer-to-inner ratio changes by $R=e^{t_n d}$ and the conjugate-label ratio changes by $Q=e^{i\theta_n d}$. Their moduli give $\Delta X=\log\lvert R\rvert/t_n$ and $\Delta Y=-\log\lvert Q\rvert/\theta_n$. Starting from known ordinates, a Newton step predicted the direction of the finite zero’s displacement from layer 40 to 41 and from layer 60 to 61 within $1.75\times10^{-5}$ radians in each test. [Quartet ratios, seeds and interval checks](../../archive/2026-11-17-quartet-angle-v001/README.md)

For the coupling recursion I took the difference of the fourth-order expansions of the two ordered returns. A scan using 2,048 quartet levels and 72 coupling terms enclosed a sign change. A separate evaluation of Hardy’s function narrowed the bracket to $T=32.935061587739189691\pm4.30\times10^{-19}$. [Return expansions, finite scan and Hardy check](../../archive/2026-11-17-quartet-return-recursion-v001/README.md)

<div><a name="read-period-640" id="user-content-read-period-640"></a></div>

<div><a name="oriented-period-640-return"></a><a name="36-inverting-two-spectral-traces-on-the-period-640-orbit"></a></div>

### 3.6 Recovering the period-640 return angle from two spectral traces

Two labeled reciprocal-root sums determine which side of $-\pi/2$ the return angle lies on.

[![The two spectral traces at the native period-640 angle as it turns clockwise by π/6 and back.](../figures/ordered-turn.gif)](../figures/ordered-turn.png)

<a name="fig-5"></a>**Fig. 5. Recovering the side of the return angle from two spectral readings.** On the left I turn the native period-640 angle $\theta_0$ clockwise by $\pi/6$ along the gold arc, then retrace it. On the right the teal circle reads $M_+(\theta)$ and the rust square reads $M_-(\theta)$ at the same angle. Above $-\pi/2$ the circle lies higher. Below $-\pi/2$ the square lies higher. They agree at $-\pi/2$, so their order distinguishes the two sides throughout this turn. [Static trace comparison](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/trace_order.png)

<details>
<summary>The two trace readings and the recovered angle</summary>

I measure the angle of an actual period-640 return on the centerline $L=iy$. Iterating $G_y=g_{iy}^{320}$ from the cap $1$ selects a periodic point $p_y$. The principal argument $\theta=\arg G_y'(p_y)$ is the rotation of a tangent vector after the 640 exponential stages, in radians with counterclockwise positive. At $y_0=0.509892982511772$ it is about $-1.50505761241$. [Period convention and the cap-selected cycles](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L554-L604) · [Derivative of the full lap](../../lean/SuperZeta/Oriented/OrderedStages.lean)

I encode a probe angle $a$ by multiplying the two exponential outputs by $e^{ia}$ and $e^{-ia}$, respectively. The auxiliary multiplier-one equation for these marked stages is $u=\sigma\cos(u+a)$. With $q_{\sigma,a}(u)=u-\sigma\cos(u+a)$, the squared determinant at $\cos a\ne0$ is

$`\displaystyle E_{\sigma,-a}(u^2)=\frac{q_{\sigma,a}(u)q_{\sigma,a}(-u)}{\cos^2 a}.`$

For the positive sign the sum of the reciprocal zeros converges absolutely and equals $M(a)=-E_{+,-a}'(0)=2/(1-\sin a)$. The unshifted determinants agree at angles reflected across $-\pi/2$ modulo $2\pi$, even with both signs retained. I measure the positive-sign spectrum at two labeled offsets to recover the unit direction $e^{i\theta}$.

$`\displaystyle M_\pm=M(\theta\pm\pi/6),\qquad S_\pm=1-2/M_\pm,\qquad \cos\theta=S_+-S_-,\qquad \sin\theta=\frac{S_++S_-}{\sqrt{3}}.`$

With both probes regular, $S_\pm=\sin(\theta\pm\pi/6)$. In $-2\pi/3<\theta<-\pi/3$, $M_+>M_-$ places $\theta$ above $-\pi/2$ and $M_+<M_-$ places it below. At $-\pi/2$ the two traces are both $8-4\sqrt3$. [Proof from the complete zero set](../../lean/SuperZeta/Oriented/SpectralInverse.lean) · [Reflection of the squared determinant](../../lean/SuperZeta/Oriented/PhaseSymmetry.lean)

I tested this by turning the measured angle clockwise by $\pi/6$, solving for the parameter on the same centerline branch, and evaluating both traces again. The table gives rounded values from the interval enclosures. [Interval record](../../archive/2026-11-19-oriented-return-v001/data/quarter_probe.json)

| Measurement | Return angle in radians | $M_+$ | $M_-$ |
| --- | ---: | ---: | ---: |
| Original orbit | −1.50505761241 | 1.092114930 | 1.054295998 |
| After the clockwise turn | −2.02865638801 | 1.001081173 | 1.285503688 |

Decoding the second pair and adding back $\pi/6$ recovered $y_0$ in an interval of width below $10^{-29}$. The cap marks the starting point, and the ordered map recovers $U=LQ$ and $V=-LP$ at every step. All 1,280 returned exponent enclosures overlap their original partners. In the interval $0.50989298230\le y\le0.50989298314$, 448-bit interval arithmetic proves cap attraction, primitive ordered period 640, and a positive angle derivative. Lean proves the spectral inverse and the round trip for regular readouts on a continuous branch with positive derivative and the target angle in range. It also checks the printed rational return bounds. [Full proof, arithmetic comparison with Liu, and replay](../../archive/2026-11-19-oriented-return-v001/README.md)

The round trip above turns by $\pi/6$ from the measured orbit angle. At the two *absolute* angles $a=-\pi/6$ and $a=+\pi/6$, the reference spectra give the same function $\pi^{-w}(3^w-1)\zeta(w)$, with $w=2s$. The first dynamical trace minus the first reference trace is $0$ at the negative angle and $8/3$ at the positive angle. Following a zero as $a$ varies gives another way to distinguish the two orientations. [Derivation and phase convention](../../archive/2026-11-19-oriented-return-v001/README.md#the-arithmetic-reference-at-the-two-absolute-angles) · [Angular derivatives at the two angles](#user-content-read-liu-speed)

</details>

<div><a name="zero-transport"></a><a name="37-following-a-zero-from-one-turn-to-the-next"></a></div>

### 3.7 Continuing Hurwitz zeros from π/3 to π/4 and reusing their endpoints

A clockwise turn of $\pi/12$ radians can carry one Riemann zero to another or to a zero of $2^w-1$.

<details>
<summary>Endpoint factors, the forward trial and the earlier trajectories</summary>

I follow the intervening zeros of the symmetric Hurwitz sum. On the right Dottie flank I hold $\Re L=4.749479070945369\times10^{-8}$ fixed and vary $\Im L$ so that the period-640 return angle $\theta$ goes from $\pi/3$ to $\pi/4$. At the starting angle the plus probe has singular normalization and its inverse trace extends continuously to $1/M_+=0$. The angle traveled is $h=\pi/3-\theta$, so the shift $b=1/6+h/\pi$ runs from $1/6$ to $1/4$. [Orbit calibration](../../archive/2026-11-19-zero-transport-v001/Dottie-Off-Axis-Return/NOTES.txt)

I follow zeros of $R(b,w)=\pi^{-w}H(w,b)$, where $w=2s$ and $H(w,b)=\zeta(w,b)+\zeta(w,1-b)$. The Hurwitz function $\zeta(w,b)$ continues the series $\sum_{n\ge0}(n+b)^{-w}$ from $\Re w>1$. [The arithmetic family and its antecedents](../../archive/2026-11-19-zero-transport-v001/README.md#relation-to-prior-work)

Grouping the reduced residue classes modulo four and six gives, for $w\ne1$,

$`\displaystyle R(1/4,w)=\pi^{-w}2^w(2^w-1)\zeta(w),\qquad R(1/6,w)=2^{-w}(3^w-1)R(1/4,w).`$

The first identity gives the possible endpoints, Riemann zeros and zeros of $2^w-1$. The second lets me reset to $b=1/6$ with the same exact zero as the next seed. A zero of the moving sum is simple in $w$ when its derivative $H_w(w,b)$ is nonzero there. This gives a unique local continuation as $b$ varies. I follow it through overlapping uniqueness disks and save the landing before identifying it by its elementary factor or a Riemann zero count. [Lean proof of the reset](../../archive/2026-11-19-zero-transport-v001/Dottie-Second-Zero/ReferenceReset.lean) · [Path and endpoint checks](../../archive/2026-11-19-zero-transport-v001/README.md#verification-and-replay)

Write $\rho_n$ for the positive-height Riemann zero of index $n$ in increasing height order. The first seed came from tracing $\rho_1$ backward. I called the second, third and fourth zeros before the respective forward tests. The first failed call was for $\rho_5$. Each arrow is one sweep.

$`\displaystyle \rho_1 \longrightarrow \frac{4\pi i}{\log 2} \longrightarrow \rho_2 \longrightarrow \rho_3 \longrightarrow \rho_4 \longrightarrow \frac{8\pi i}{\log 2} \longrightarrow \rho_7.`$

The fourth-zero call hit directly. The next two sweeps skipped the fifth and sixth as endpoints and as interior points of the route. [Predictions, comparison seeds and stopping rule](../../archive/2026-11-19-zero-transport-v001/README.md#how-the-cases-were-selected)

![Paths from the third Riemann zero to the fourth, an elementary zero and the seventh. The dashed line marks real part one half.](../figures/proof-successor-paths.png)

<a name="fig-6"></a>**Fig. 6. Three successive clockwise sweeps of the Hurwitz reference.** I follow one moving zero per sweep from $\theta=\pi/3$ to $\pi/4$, taking the endpoint of each sweep as the start of the next. Teal joins $\rho_3$ to $\rho_4$, rust joins $\rho_4$ to the elementary zero $b=8\pi i/\log 2$, and purple joins $b$ to $\rho_7$. The left panel traces $w$ in the complex plane. The right plots $\Re w$ against the turn angle. The dashed line marks $\Re w=1/2$ in both. The fifth and sixth Riemann zeros are skipped on this route. [Archived paths and frozen predictions](../../archive/2026-11-19-zero-transport-v001/README.md)

McPhedran, Botten and Nicorovici plotted the same Hurwitz family in 2007. Their parameter is $a=1-b$, so my clockwise sweep reads their figures from $a=5/6$ to $a=3/4$. Figures 2b, 3a, 3b and 4 give the four individual arcs from $4\pi i/\log 3$ through the first Riemann zero, the base-two address, the second zero and the third. I matched the figures by following their labeled zeros from $a=1/2$ to both anchors. Reusing the endpoints joins arcs of distinct trajectories. [Original paper, §3 and Figures 2–4](https://doi.org/10.1098/rspa.2006.1763) · [Five figure identifications and their checks](../../archive/2026-11-19-zero-transport-v001/Dottie-Transport-Reversibility/PRIOR-WORK.md)

After the forward trial I traced $\rho_5$ and $\rho_6$ backward and replayed both paths forward. Their seeds are $10\pi i/\log 3$ and $12\pi i/\log 3$, respectively. Both come from $3^w-1$ at $b=1/6$. An imaginary-axis endpoint at $b=1/4$ satisfies $2^w=1$, and there is no shared nonzero address between these two lattices, since no positive powers of two and three agree. Each reverse path is simple and regular throughout the sweep, so it fixes the sole predecessor under regular continuation. A direct turn can reach either zero from its base-three seed. The chain of reused endpoints skips them because it cannot supply those seeds. [Inverse calculation, proof and replay](../../archive/2026-11-19-zero-transport-v001/Dottie-Transport-Reversibility/README.md) · [Question log](#user-content-read-questions)

</details>

#### Three crossings of the critical line on the path from the fourth zero

The path starting at $\rho_4$ crosses $\Re w=1/2$ three more times. At each crossing the moving Hurwitz sum vanishes and ordinary Riemann zeta has positive magnitude.

<details>
<summary>Critical-line crossing angles and heights</summary>

The last two crossings form the narrow upper loop. I give the clockwise angle traveled as $h$, so the signed change in angle is $-h$. The displayed interior angles are rounded.

| Clockwise angle $h$ | Event | Height | Ordinary zeta magnitude |
| --- | --- | ---: | ---: |
| $0$ | Start at the fourth zero | 30.424876 | 0 |
| $0.034097675\pi$ | Cross to the left | 33.035367 | 0.142187 |
| $0.070080843\pi$ | Cross to the right | 35.225270 | 2.920990 |
| $0.071086383\pi$ | Cross back to the left | 35.325132 | 2.938889 |
| $\pi/12$ | Reach the elementary zero | 36.258881 | 4.055336 |

[Native angles, turns and exact elementary addresses](../../archive/2026-11-19-zero-transport-v001/Dottie-Transport-Reversibility/rotations.md) · [Directed crossing enclosures](../../archive/2026-11-19-zero-transport-v001/Dottie-Transport-Reversibility/blue-crossings.json) · [Download the interactive route explorer](https://github.com/NuckyDucky/The-Super-Zeta-Function/raw/refs/heads/main/archive/2026-11-19-zero-transport-v001/order-of-the-turns.html)

</details>

<div><a name="38-why-the-sixth-path-folds-back"></a></div>

### 3.8 Three crossings of height 37.25 on the sixth Hurwitz path

On the branch from $12\pi i/\log 3$ to the sixth Riemann zero, two horizontal tangencies make the path pass height $37.25$ three times.

<details>
<summary>Velocity, acceleration and the three crossings</summary>

It first rises through that height left of the imaginary axis, then falls through it farther left, then rises through it to the right. From crest to trough the tangent turns from due left to due right, counterclockwise by $\pi$ radians. Over that arc the input turns clockwise by only $0.04283506$ radians.

On the simple branch $H(w,b)=0$, the velocity is $dw/dh=-H_b/(\pi H_w)$ when $h$ is in radians. The interactive replay tabulates velocities and accelerations per clockwise degree. To express those values per radian I multiply them by $180/\pi$ and $(180/\pi)^2$, respectively.

[![The sixth path crosses the same height three times. Click to compare the derivatives.](../figures/proof-sixth-passes.png)](https://nuckyducky.github.io/The-Super-Zeta-Function/)

<a name="fig-7"></a>**Fig. 7. Three passes of the sixth path through the same height.** At left I number the passes through $T=37.25$ in order. The filled diamonds mark the local height extrema. The open square marks a separate event near $-0.14560046+37.21759523i$, where the path visits the same complex point twice with tangent lines about $0.713809$ radians apart. On the right I center the clockwise angle at each pass. The signs of the three slopes show that the path rises through $37.25$ in teal, falls through it in rust, and rises through it again in purple. [Open the interactive graph](https://nuckyducky.github.io/The-Super-Zeta-Function/) · [Derivative formulas, interval proofs and replay](../../archive/2026-11-19-sixth-passes-v001/README.md)

</details>

<div><a name="39-what-one-hurwitz-term-remembers-about-the-orbit"></a></div>

### 3.9 Distinguishing the two visits with one Hurwitz summand

One complex number distinguishes the two visits to the sixth path’s self-intersection. I kept the first summand $A=\zeta(w,b)$ and hid the position, the angle and both spectral traces.

<details>
<summary>The first summand at the two visits</summary>

One reading selected the visit leaving at $2.482077$ radians, up and left. The other selected the visit leaving at $0.054293$ radians, almost due right. Angles are counterclockwise from the positive real axis. On the calibrated right flank the recovered shift identifies the marked period-640 orbit for each visit. [Blind inputs, decoded directions and orbit enclosures](../../archive/2026-11-19-single-term-inverse-v001/README.md#the-experiment)

Elsewhere on the same sweep, the first summand takes the same value at two distinct positions. The corresponding orbit multiplier moduli are $0.19009231$ and $0.18425549$, giving different contraction rates. I checked the entire $\pi/12$ sweep and found exactly one such pair. Its two zero positions differ, so $(w,A)$ identifies every visit on this sweep. [Graph of the two crossings and proof](../../archive/2026-11-19-single-term-inverse-v001/README.md#where-the-single-reading-agrees-twice)

</details>

<div><a name="310-what-a-full-turn-changes-near-the-sixth-zero"></a></div>

### 3.10 Transport near the sixth landing and the two logarithms of a lap

The trough is the last local minimum of $\Im w$ along the sixth moving zero. From that angle to $\theta=\pi/4$, I follow the zero and 16 neighboring starting points.

<details>
<summary>The sixth trajectory and its neighboring paths</summary>

Each path keeps its own starting value of $H(w,b)$ as the angle changes, so only the path that starts at zero is required to stay on the zero set. With equal scales on the real and imaginary axes, the distance between positions at the same angle measures how much the two paths have separated.

![Sixteen nearby paths and the sixth moving zero, with starts, endpoints and arrows in the complex plane.](../figures/proof-complex-turn.png)

<a name="fig-8"></a>**Fig. 8. Sixteen nearby starts on the final turn of the sixth path.** From each open circle I follow the curve that keeps its initial Hurwitz sum $H(w,b)$ fixed until the clockwise turn reaches $h=\pi/12$ (diamond). Color identifies starting height. The dark path has $H=0$ throughout, so its last height minimum leads to the sixth Riemann zero (star). The neighboring paths carry their own initial values through the same turn. [Trajectories and continuation rule](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/THESIS.md)

For a closer comparison I placed a point $10^{-6}$ to the right of the zero at the trough. In units of $10^{-6}$, the displacement vector starts at $(1,0)$ and ends at $(0.247209,0.905975)$, with direction $1.304416$ radians. Its length reaches a unique maximum of $1.233768546$ at $h\approx0.249559635032$, returns to $1$ at $h\approx0.259687877153$, and ends at $0.939096964$. [Proof for this pair](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/neighbor_proof.txt) · [Interval bounds](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/neighbor_proof.json) · [Distance plotted against the turn angle](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/two_paths.png)

![Magnified complex displacement from the moving zero to its neighbor, measured in millionths on equal axes.](../figures/proof-complex-offset.png)

<a name="fig-9"></a>**Fig. 9. Separation from a point launched one millionth to the right.** I subtract the moving zero from its neighboring path at each common angle and plot the complex difference on axes magnified by $10^6$. The open circle is the initial separation $\Delta=1$. At the filled circle near $h=0.2496$ the distance is about $1.234$ times its initial value. The endpoint diamond lies inside the dashed unit circle at $\Delta\approx0.2472+0.9060i$, so the paths finish closer together, with most of their remaining separation in height. [Displacement record](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/neighbor_proof.json)

</details>

#### Length changes and folds in the plane map

Length change measures how two nearby starting points separate during the turn. An infinitesimal segment beginning at the trough ends at $0.93910$ times its starting length.

<details>
<summary>Length ratios and square-root folds across the grid</summary>

At $0.075+36.75i$ the factor is $0.28613$, while at $-0.525+37.3125i$ it is $8.0752$. Directed intervals bound both nonzero-level examples. Colors in the grid estimate this ratio at each starting point. Download the interactive map with **Download raw file** to inspect any of the 10,961 starts and its endpoint. [Plane map and derivative](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/plane_notes.md) · [Two certified paths](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/plane_anchors.json) · [Interactive complex-plane map](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/complex_explorer.html)

I extended the grid to $-2\le\Re w\le2$ and $34\le\Im w\le40$. Of these starting points, 38,649 passed the two-resolution comparison and 152 were flagged. Off-white means the length factor is near one. Crosses mark disagreement between resolutions or a level residual above tolerance. In the closeup, all 37 flagged centers reached regular endpoints under interval continuation. Two adjacent inputs at height $36.7875$ start $0.0125$ apart and end $1.72036$ apart, even though infinitesimal lengths shrink to less than half at both inputs. [The wider sample](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/plane_wide.json) · [All 37 verified centers and the two-point comparison](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/staircase.json)

Inside each of those 37 cells I found a point whose two solutions coalesce at a square-root fold. All 37 paths approach the same continued critical branch with the same sign of the local square root. [Moving critical branch and the 37 collisions](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/gray_collision.json)

[Wider field](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/plane_wide.png) · [Closeup](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/plane_strain.png) · [Complete starting and final grids](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/plane_grid.png)

</details>

#### Two destinations at fixed Hurwitz shift

From $37i$ the ordered stage arguments lead to Riemann zero six, while the principal argument leads to the elementary zero $8\pi i/\log 2$.

<details>
<summary>The two logarithms and their certified limits</summary>

Here I hold $b=1/4$ fixed, so the function is $f(w)=H(w,1/4)=2^w(2^w-1)\zeta(w)$. On the continued right-flank orbit the full 640-stage multiplier has modulus $|\mu|\approx0.18397133$ and principal argument $+\pi/4$. To find how it turned stage by stage, I follow $z_j$ to $e^{a_jz_j}$ for $a_j=-L,L,-L,L,\ldots$ and add the following logarithms of the derivatives.

$`\displaystyle \ell_{\mathrm{ord}}=\sum_{j=0}^{639}\bigl(\mathrm{Log}\, a_j+a_jz_j\bigr), \qquad e^{\ell_{\mathrm{ord}}}=\mu,\qquad \Im\ell_{\mathrm{ord}}=-7\pi/4.`$

The imaginary parts differ by one revolution. I use either logarithm $\ell$ to prescribe a continuous path for the **value** of $f$, then follow the inverse of $f$ starting at $w_0$. At an integer lap $m$ both value paths give $\mu^m f(w_0)$. Between laps they wind differently. [448-bit stage sum and direct multiplier product](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/phase_lift.json)

$`\displaystyle f(w(t))=e^{t\ell}f(w_0),\qquad w(0)=w_0,\qquad \frac{dw}{dt}=\ell\,\frac{f(w)}{f'(w)}\quad(f'(w)\ne0).`$

For every $|w_0-37i|\le10^{-6}$, continuing with the principal logarithm converges to the elementary zero $8\pi i/\log 2$. The ordered logarithm leads to $\rho_6$. The two inverse branches meet at a simple critical point of $f$ near $0.235950387+36.945179676i$. The loop formed by the first lap of the two value paths at $w_0=37i$ winds once around its critical value. [Derivation and proof](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/THESIS.md) · [Whole-disk convergence](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/basin_certificate.json) · [The two branches](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/critical_branches.json)

![The destinations reached by the two logarithms on the same grid of starting points.](../figures/proof-basins.png)

<a name="fig-10"></a>**Fig. 10. Destination of each start under the two logarithmic lifts.** I use the same starting grid for the principal lift ($+\pi/4$ per lap, left) and the ordered lift ($-7\pi/4$ per lap, right). Color identifies the limiting zero estimated for each start, with gray for undecided samples. The white curves follow the dot at $37i$ for four laps. The two stars are the destinations in view. For every start within $10^{-6}$ of $37i$, the interval proof gives $8\pi i/\log 2$ under the principal lift and $\rho_6$ under the ordered lift. [Measurements and certificate](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/THESIS.md)

</details>

#### Predicting endpoints from position, velocity and acceleration

From the last trough on the sixth path, one quadratic extrapolation accounts for $`27.23\%`$ of the remaining rise.

<details>
<summary>Quadratic extrapolation and repeated derivative updates</summary>

Recomputing velocity and acceleration in 64 steps reduces the complex endpoint error from $0.274054$ to $0.000076581$. I made the same comparison on ten previously traced branches, hiding their known endpoints during extrapolation. I then fixed two new base-three seeds, a cutoff and a scoring rule before evaluating them. With $\pi/1440$ radians left, the error was $0.00001901$ for seed 7, which reached the fifth base-two address, and $0.00030671$ for seed 8, which reached Riemann zero 11. Both predictions met the $0.001$ threshold and identified the endpoint family. [Retrospective ten-branch trial](../../archive/2026-11-19-dottie-plane-atlas-v001/landing/README.md) · [Pre-evaluation protocol](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/a739bf30c0db09774d4fd3681596a1821f31d081/protocols/2026-11-19-dottie-plane-holdout.json) · [Two-seed results](../../archive/2026-11-19-dottie-plane-atlas-v001/holdout/README.md)

</details>

<div><a name="read-liu-speed" id="user-content-read-liu-speed"></a></div>

### 3.11 Liu’s zero-free bound and the angular velocity at ±π/6

At the absolute angles $a=\pm\pi/6$ my symmetrized Hurwitz reference has a zero at each simple nontrivial Riemann zero $\rho$.

<details>
<summary>Two signed velocities and their bounds</summary>

Turning the angle moves the Hurwitz zero. The symmetry $R(-a,w)=R(a,w)$ traces the same local arc in reverse, so equal positive increments from those two angles send the zero in opposite directions. I use Liu’s bound on the real part of $\rho$ to bound the common speed after scaling by the local slope of Riemann zeta. [Statement, proof and independent checks](../../archive/2026-11-20-liu-angular-velocity-v002/README.md)

Write $b=1/2-a/\pi$. The reference is $`R(a,w)=\pi^{-w}[\zeta(w,b)+\zeta(w,1-b)]`$ with $w=2s$. At $+\pi/6$ the shifts are $1/3$ and $2/3$. Their sum gives the Riemann factor. Differentiating in $a$ subtracts the two terms and gives the odd Dirichlet character $\chi_{-3}$, whose values on $1,2,0$ modulo three are $1,-1,0$. If $V_+$ and $V_-$ are the derivatives $dw/da$ of the zero at the two angles, I obtain

$`\displaystyle V_-=-V_+,\qquad V_+=-\frac{3\rho}{\pi\zeta'(\rho)}\,\frac{L(1+\rho,\chi_{-3})}{1-3^{-\rho}}.`$

I divide out the explicit factor $`\lvert\rho/\zeta'(\rho)\rvert`$ to compare speeds across heights. With $`S=\lvert V_+\rvert\,\lvert\zeta'(\rho)\rvert/\lvert\rho\rvert`$, the 7/8ths theorem gives $0.11197\lt S\lt45.333$. Liu’s endpoint $B_{\ast}=0.8733458561067185768\ldots$ tightens this to **$0.11325\lt S\lt44.270$ at every simple nontrivial Riemann zero**. For the sixth zero I get $V_+\approx5.82821-7.57291i$ per radian and $S\approx0.49229847$. A positive angular increment then moves the zero left and up from the negative angle, or right and down from the positive angle. [Euler-product bounds and verification scope](../../archive/2026-11-20-liu-angular-velocity-v001/README.md#from-a-bound-on-position-to-a-bound-on-speed) · [First ten zeros at 256 bits](../../archive/2026-11-20-liu-angular-velocity-v001/bounds.json) · [Direct perturbations of the angle](../../archive/2026-11-20-liu-angular-velocity-v002/tangents.json) · [Lean transfer and path reversal](../../lean/SuperZeta/Oriented/LiuEndpointTransfer.lean)

My Lean proof takes the Dirichlet half-plane bound as a hypothesis. Bebel proves that input in a separate Lean build. Here I check that Liu’s optimization equation gives the same endpoint polynomial, specialize the bound to Riemann zeta and apply it at both signed angles. I obtain the speed inequalities from Euler-product estimates in the written derivation. [Formal scope and independent build](../../archive/2026-11-20-liu-angular-velocity-v002/README.md) · [Transfer theorem and its hypothesis](../../lean/SuperZeta/Oriented/LiuEndpointTransfer.lean)

</details>

<div><a name="read-speed-moment" id="user-content-read-speed-moment"></a></div>

### 3.12 Mean squared speed at Riemann zeros

The three Dottie windows give mean squared normalized speeds of about **0.475, 0.920 and 1.422**.

<details>
<summary>Three interval means and the cumulative estimate</summary>

I can distinguish the first two from their heights alone. Across the entire first critical-line segment, the squared arithmetic value stays below 0.644. Across the entire second segment, it stays above 0.798. [Individual zero enclosures and bounds over the segments](../../archive/2026-11-20-hurwitz-speed-mean-square-v001/README.md#three-short-intervals-with-every-zero-counted)

At a simple zero, squared normalized speed is the squared modulus of $`G(z)=(3/\pi)L(1+z,\chi_{-3})/(1-3^{-z})`$. At a multiple zero I can still evaluate $G$. Counting every zero with multiplicity, the average of $`\lvert G\rvert^2`$ up to height $T$ tends to $`13\zeta(3)/\pi^2=1.583319767\ldots`$. Its first correction comes from pairs of indices whose ratio is a prime power in Landau’s explicit formula. For the first 1,024 zeros the two-term value is 1.31503 and the measured mean is 1.32677. I also bound the mean restricted to simple zeros in shrinking windows using the arithmetic value at the window center. [Derivation, scope and open question](../../archive/2026-11-20-hurwitz-speed-mean-square-v001/README.md) · [Reproducible computation](../../archive/2026-11-20-hurwitz-speed-mean-square-v001/verify_moments.py)

</details>

<div><a name="read-two-inputs" id="user-content-read-two-inputs"></a></div>

### 3.13 Two complex inputs and recovery of the quartet spectrum

At one fixed real part, the two imaginary inputs let me read the radii and angles of the squared roots separately.

[![Two imaginary shifts at real part one. The change in the complex sum from the quartet angles vanishes on the dotted diagonal k equals minus h. Open the interactive map.](../figures/proof-two-input.png)](https://nuckyducky.github.io/The-Super-Zeta-Function/two-input/)

<a name="fig-11"></a>**Fig. 11. Angular contribution to the two-input spectral sum.** I vary $h$ and $k$ in $x=1+ih$ and $y=1+ik$. Holding $h-k$ fixed preserves the radial phase. Color measures how much the complex sum changes when I restore the root angles, from zero in cream to the largest change in dark purple. The dotted line $k=-h$ gives exact angular cancellation. At the two opposite-sign circles the sums are about $2.685091+1.968416i$ and its conjugate. At the two same-sign circles the sums agree and the angular change is about $0.022907$. [Explore all four readings](https://nuckyducky.github.io/The-Super-Zeta-Function/two-input/) · [Full-resolution figure](../../archive/2026-11-20-two-input-map-v001/two-input-dottie-map.png) · [Figure source and truncation bound](../../archive/2026-11-20-two-input-map-v001/README.md)

<details>
<summary>The two-input identity and finite-precision reconstruction</summary>

I show the separation across the whole plane, then test how much of the first pair I can recover from five readings.

For each squared root $\lambda$ I evaluate its principal power at two complex inputs, multiply the first reading by the conjugate of the second, and sum over roots. For ordinary Dirichlet powers the same operation pairs equal integers and gives $\zeta(x+\bar y)$. My indices are complex roots, so each contributes its argument as well as its modulus. [Hedenmalm, Lindqvist and Seip, §4.3, kernel formula](https://arxiv.org/pdf/math/9512211#page=17) · [Source comparison](../../archive/2026-11-20-hurwitz-speed-mean-square-v002/README.md)

$`\displaystyle \mathrm{Sz}_E(x,y)=\sum_{E(\lambda)=0}\lambda^{-x}\overline{\lambda^{-y}}, \qquad \Re x+\Re y>\tfrac12.`$

**Recovery from one plane.** The four roots $u,-u,\bar u,-\bar u$ give two squared roots $R e^{i\psi},R e^{-i\psi}$. Set $x=r+ih$ and $y=r+ik$ with $r>1/4$. This pair contributes

$`\displaystyle 2R^{-2r}e^{-i(h-k)\log R}\cosh\!\big((h+k)\psi\big).`$

As I vary $h-k$, the oscillation has frequency $\log R$. Once I isolate that frequency, varying $h+k$ gives the angles at that radius. Exact values across the whole plane at one fixed $r$ determine the squared roots and their multiplicities. Setting $y=0$ in the defining sum recovers my original one-input super zeta where its series converges. [Full-plane proof and principal logarithms](../../archive/2026-11-20-hurwitz-speed-mean-square-v001/two-input-spectrum.md#a-plane-indexed-by-two-imaginary-displacements)

**Recovery from five readings.** Here I set $h=k$, write $\eta=h+k$, and use five real totals. At $r=16$ I take $\eta=0,1,2$. At $r=17$ I take $\eta=0,1$. Subtracting the $\eta=0$ reading cancels the real Dottie root. A bound on the higher levels isolates the first conjugate pair. With the archived readings I obtain a modulus between 9.458388942732 and 9.458388942826 and a positive argument between 1.257969768180 and 1.257969768339 radians. The conjugate has the negative argument. Solving the original cosine equation separately gives values inside both intervals. [Five inputs, tail bound and inverse](../../archive/2026-11-20-hurwitz-speed-mean-square-v001/two-input-spectrum.md#recovering-the-first-nonreal-pair-from-five-full-readings)

Two totals near $8.49\times10^8$ differ by only $1.20\times10^{-33}$. I rounded each of the five stored intervals outward to the indicated number of significant digits and repeated the inverse at 320 bits. The table gives the approximate *widths* of the resulting enclosures.

| Significant digits per reading | Width in modulus | Width in angle (radians) |
| ---: | ---: | ---: |
| 42 | Unresolved | Unresolved |
| 43 | 0.80 | 0.00393 |
| 51 | $8.08\times10^{-9}$ | $1.98\times10^{-10}$ |
| 52 | $8.92\times10^{-10}$ | $1.63\times10^{-10}$ |

At 52 digits both widths are below $10^{-9}$ for these five readings. The full-plane uniqueness and tail bounds have written proofs. Lean proves conjugation exchanges the inputs of each root term, and checks the double-shift identity used to isolate its angle. The numerical replay rounds all five readings outward and repeats the inversion. [Conjugation and principal powers in Lean](../../lean/SuperZeta/Oriented/TwoInputSpectrum.lean#L18-L32) · [Double shift and isolated angle in Lean](../../lean/SuperZeta/Oriented/TwoInputSpectrum.lean#L41-L49) · [Outward-rounding replay](../../tools/replay_two_input_results.py) · [Original intervals](../../archive/2026-11-20-hurwitz-speed-mean-square-v001/two-inputs.json)

</details>

<div><a name="4-strengthening-the-78ths-and-liu-bounds-in-three-height-intervals"></a><a name="a-local-strengthening-of-the-seven-eighths-theorem"></a><a name="local-zeta-result"></a><a name="a-local-strengthening-of-the-78ths-theorem"></a><a name="4-a-local-strengthening-of-the-78ths-theorem"></a></div>

<div><a name="read-zero-counts" id="user-content-read-zero-counts"></a></div>

## 4. A local strengthening of the 7/8ths and Liu bounds in three Dottie height windows

I used the period-640 orbit to fix $T_D\approx4.526119322478\times10^{12}$ before evaluating Riemann zeta there. Write $w=\beta+it$. At arbitrary height, Liu’s theorem and reflection put each nontrivial zero in $1-B_{\ast}\le\beta\le B_{\ast}$. In the three intervals below I can replace that whole range by **$\beta=1/2$**. For each window I compared the count around its boundary with the increase in the cumulative count across the critical strip. The two calculations agree on totals of 2, 5 and 4, and disjoint sign changes on the critical line account for all eleven. Setting $\beta=1/2$ in the speed estimate of §3.11 now gives $0.33217\lt S\lt4.76646$ for each of these eleven zeros. [Liu, Theorem 1.1](https://hexagonmath.org/pdf/2611.00421v1#page=2) · [Speed bound on the critical line](../../archive/2026-11-20-liu-angular-velocity-v001/README.md#from-a-bound-on-position-to-a-bound-on-speed)

A **simple zero** $\rho$ is a point where $\zeta(\rho)=0$ and $\zeta'(\rho)\ne0$. Near that point $\zeta(w)$ has exactly one factor of $w-\rho$, so it contributes one to a count taken around the boundary. In the first window I found two disjoint intervals on the critical line where Hardy’s real function changes sign, each guaranteeing a distinct zero. The boundary count is exactly two including multiplicity, which accounts for the entire window and forces both zeros to be simple.

| Interval in Riemann height $t$ | Simple zeros on $\beta=\tfrac12$ | Off-critical-line zeros | Certificate |
| --- | ---: | ---: | --- |
| $\lvert t-T_D\rvert\le\tfrac14$ | 2 | 0 | [Count and endpoint signs](../../archive/2026-11-20-liu-angular-velocity-v002/README.md#where-the-zero-locations-are-sharper) |
| $\lvert t-2T_D\rvert\le\tfrac12$ | 5 | 0 | [Second height](../../archive/2026-11-18-superzeta-distance-v001/README.md) |
| $\lvert t-3T_D\rvert\le\tfrac12$ | 4 | 0 | [Third height](../../archive/2026-11-18-superzeta-distance-v001/README.md) |

![The three certified height intervals on the same offset axis, with two, five and four critical-line zeros respectively.](../figures/proof-riemann-windows.png)

<a name="fig-12"></a>**Fig. 12. All eleven critical-line zeros in the three height windows.** I subtract $kT_D$ from the heights in each row so the three windows share one horizontal scale. The bar spans the tested interval, and each circle marks the midpoint of a disjoint bracket where Hardy’s function changes sign. The independent total counts, including multiplicity, are 2, 5 and 4 from top to bottom. Those equal the numbers of brackets, so each bracket contains one simple zero on the line and the windows contain no others. [Bracket endpoints, signs and cumulative counts](../../archive/2026-11-20-liu-angular-velocity-v002/windows.json)

I also tested whether the Dottie rule picks heights *closer* to a Riemann zero than nearby controls. Each of 32 inputs had two controls. Of the 64 comparisons, 20 favored Dottie, 16 favored a control, and 28 stayed unresolved because 14 inputs did not pass the orbit check. The preregistered majority across all 64 comparisons is still open. [Frozen rule](../../archive/2026-11-18-clock-local-controls-protocol-v001/README.md) · [All 32 inputs and their outcomes](../../archive/2026-11-18-clock-proximity-results-v001/README.md)

<div><a name="how-the-iteration-gives-the-height"></a><a name="selection-of-the-test-height"></a></div>

### How the marked period-640 lap sets the test height

I fixed $T_D$ from one full turn of a phase measured using three Dottie parameters.

<details>
<summary>The three parameters and the height formula</summary>

Two lie at the same height on opposite sides of the spire, $L_\pm=\pm\eta+iy$. The third is their midpoint $L_0=iy$. I used the exact decimals $\eta=4.749479070945369\times10^{-8}$ and $y=0.509892982511772$. At each parameter the cap $(1,1)$ approaches a cycle of primitive scalar period 320 under the two-update return in each coordinate. One lap along a phase takes 640 exponential stages, 320 of each sign. [Height rule and frozen inputs](../../archive/2026-11-17-dottie-grid-match-v001/README.md#nomination-before-forecasting)

I first tried choosing a height from one cycle at a time. If $k$ is the winding of its tangent and $\mu$ its multiplier, that candidate was $2\pi\lvert k\rvert/(-\log\lvert\mu\rvert)$. Ordinary zeta had a certified nonzero value at each candidate from the two flanks and the midpoint. The height used here instead compares a marked stage across those three cycles. [First height rule and all three readings](../../archive/2026-11-17-quartet-return-recursion-v001/README.md#dottie-clock-test)

For a stage $E(z)=e^{\pm Lz}$, the derivative in the logarithmic output coordinate is $E'(z)/E(z)=\pm L$. I multiply these coefficients for the 320 occurrences of one sign in the lap. Comparing a flank with the midpoint gives the modulus ratio $(|L_\pm|/|L_0|)^{320}$, whose logarithm is $\delta_{\mathrm{clock}}=160\log(1+(\eta/y)^2)$. A separate check of the ordinary full-return tangent gave winding of magnitude one at each flank. Before evaluating zeta I used $e^{it\delta_{\mathrm{clock}}}$ as the phase at Riemann height $t$ and took its first positive full turn, $T_D\delta_{\mathrm{clock}}=2\pi$.

$`\displaystyle T_D=\frac{2\pi}{160\log(1+(\eta/y)^2)} =4{,}526{,}119{,}322{,}477.945393\ldots .`$

I compared the first window with one of the same width centered at the nearest multiple of $\pi$. That control contained three zeros, all on the critical line. [Winding and matched comparison](../../archive/2026-11-17-dottie-grid-match-v001/README.md#forecast-and-directed-counts)

</details>

<div><a name="what-the-three-windows-tell-me"></a><a name="certified-counts-in-the-three-windows"></a></div>

### Eleven simple critical-line zeros in the three height windows

Each zero below has the form $\rho=1/2+i(kT_D+u)$. For example, the first window contains one zero about $0.199139$ below $T_D$ and another about $0.082089$ above it.

<details>
<summary>Zero counts, brackets and distances in each interval</summary>

I give the midpoints of the certified height brackets rounded to six decimals. The linked record retains both rational endpoints for each zero. [Exact brackets and Hardy signs](../../archive/2026-11-20-liu-angular-velocity-v002/windows.json)

| Center | Height offsets $u$ within that window |
| --- | --- |
| $T_D$ | −0.199139, +0.082089 |
| $2T_D$ | −0.238174, −0.024279, +0.080224, +0.355996, +0.493434 |
| $3T_D$ | −0.481659, −0.335074, +0.016093, +0.183093 |

I counted every zero in each rectangle, including multiplicity, and found the same number of distinct critical-line zeros from disjoint intervals where Hardy’s $Z(t)$ changes sign. Write $w=\beta+it$. OpenAI’s Theorem 1.1 excludes zeros for $\beta>7/8$, and reflection gives $1/8\le\beta\le7/8$ for every nontrivial zero. At $T_D$ my contour covers $1/16<\beta<15/16$, including both boundary lines of that strip. At $2T_D$ and $3T_D$ the rectangles cover the full width $0\le\beta\le1$. [OpenAI, Theorem 1.1](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) · [Riemann reflection](https://dlmf.nist.gov/25.4) · [First full-strip corollary](../../archive/2026-11-17-dottie-local-strip-v001/README.md#full-strip-corollary)

For the contour count I bound zeta on each boundary segment by interval arithmetic. These enclosures exclude zero and give the change of argument around the rectangle. The first-height verifier counts boxes with height offsets in $[-1/4,1/4]$ using two charts that meet at $t=T_D$. The two contours give one zero each and certify that shared edge as zero-free. At $2T_D$ and $3T_D$ I use four separate quarter-height charts per window. Their counts from bottom to top are $(0,2,1,2)$ and $(2,0,2,0)$, with both outer height endpoints and every shared edge certified zero-free. In each window I also enclose opposite signs of the real Hardy function $Z(t)$ on disjoint intervals on the critical line. At $T_D$, for example, two disjoint sign-change brackets give two distinct critical-line zeros. The contour count is exactly two with multiplicity, so each of those zeros contributes one and together they exhaust the rectangle. The same argument applies to the five brackets at $2T_D$ and the four at $3T_D$. A second proof uses FLINT’s global zero counter over guards of radius $2^{-18}$ at all six endpoints and checks all 22 Hardy signs directly. At the first height, for example, the count rises from 18,947,484,639,340 to 18,947,484,639,342. Both endpoints are zero-free because each count stays constant throughout its guard. [All three full-strip counts and signs](../../archive/2026-11-20-liu-angular-velocity-v002/windows.json). [First interval certificate](../../archive/2026-11-17-dottie-local-strip-v001/README.md#full-strip-corollary) · [Higher interval counts and independent check](../../archive/2026-11-18-superzeta-distance-v001/README.md#how-the-computations-certify-the-statements) · [FLINT's zero-counting methods](https://flintlib.org/doc/algorithms/special-functions/zeta-zeros.html)

In the super zeta coordinate $w=2s$, I count the same zeros through $F(s)=\mathcal Z(s;1)-J(s;1)=2\pi^{-2s}(2^{2s}-1)\zeta(2s)$. The factor multiplying $\zeta(2s)$ is nonzero for $0<\Re(2s)<1$, so each simple Riemann zero $\rho$ in the table gives a simple zero of $F$ at $s=\rho/2$. My three windows put the zeros of $F$ on $\Re s=1/4$, with $|\Im s-T_D/2|\le1/8$ for the first and $|\Im s-kT_D/2|\le1/4$ for $k=2,3$. The higher two certificates also check the elementary factor on the closed left edge $\Re s=0$. [Spectral reconstruction, eqs. (21)–(22)](../../docs/proofs/quartet-spectrum.md#5-a-two-variable-zeta-for-the-inverse-cosine-coupling-family) · [Full result and evidence](../../archive/2026-11-18-superzeta-distance-v001/README.md)

The counts let me measure how accurately a finite Mellin sum locates each zero. In the cell assigned to $s_i=\rho_i/2$, I remove that simple zero by dividing $F(s)$ by $s-s_i$. A lower bound on the boundary modulus of the quotient extends throughout the cell. Thus $\lvert F(s)\rvert\ge\kappa\lvert s-s_i\rvert$, with $\kappa=925/256$ at $2T_D$ and $\kappa=2407/512$ at $3T_D$. At a zero of an approximation with uniform error $\eta$, the distance to $s_i$ is at most $\eta/\kappa$. With 21 regrouped Mellin blocks I get one root per cell, within $6.0\times10^{-59}$ and $7.1\times10^{-59}$ of its limiting root in the two respective windows. [Residual and distance proof](../../archive/2026-11-18-superzeta-distance-v001/README.md#local-factorization-and-position-error) · [Finite reconstruction and uniform error](../../archive/2026-11-18-superzeta-distance-v001/NATIVE.md)

</details>

### Zero proximity in the grid pilot and the 32-input test

The first matched grid window contained three critical-line zeros, compared with two in the Dottie window. In a two-height pilot, Dottie and the grid each gave the closer height once.

![For 32 inputs, two rows of symbols identify the closer height in each of 64 comparisons with the nearest Riemann zero.](../figures/proof-proximity-controls.png)

<a name="fig-13"></a>**Fig. 13. The orbit-selected height against two controls at 32 inputs.** For each input $j$ I compare the selected height with a lower control $T_-$ and an upper control $T_+$, using distance to the nearest Riemann zero. A teal circle means the selected height was closer, a rust triangle means the control was closer, and a gray cross means the orbit check left the comparison unresolved. The 64 comparisons gave 20 wins, 16 losses and 28 unresolved, leaving the proposed majority undecided. [32 inputs and both control distances](../../archive/2026-11-18-clock-proximity-results-v001/comparisons.csv)

<details>
<summary>Matched heights and the 32-input comparison</summary>

For the 32-input test I put the controls four local mean spacings above and below each selected height. Of the 18 inputs with a certified orbit, Dottie beat both controls at seven, beat one at six, and beat neither at five. [Pilot](../../archive/2026-11-18-clock-proximity-results-v001/pilot/README.md) · [Selection rule](../../archive/2026-11-18-clock-local-controls-protocol-v001/README.md) · [Every comparison](../../archive/2026-11-18-clock-proximity-results-v001/README.md)

</details>

<div><a name="the-factorial-correction"></a><a name="5-the-factorial-correction"></a></div>

<div><a name="read-factorial" id="user-content-read-factorial"></a></div>

## 5. The factorial correction

I weight the radius $R_n$ of each quartet by the fraction of two independently chosen sign histories that both balance. The resulting level $\Lambda_n$ falls below its integer label $n$ by a distance tending to $1/4$. The factorial weight accounts for that limiting displacement. The actual radii determine a finer effect, a Hurwitz sign change between levels 28 and 29 that disappears on the grid $R_n=2\pi n$. The same factorial weight also gives an exact series for the error in Stirling’s approximation to a single $n!$.

<div><a name="what-the-quarter-measures"></a></div>

### A quarter-step displacement in the normalized levels

The difference between the quartet index $n$ and its weighted level $\Lambda_n$ tends to $1/4$.

<details>
<summary>The balanced sign count and its first correction</summary>

The displaced levels in this section come from weighting each actual quartet radius by two balanced sign counts.

The fraction of words of length $2n$ with equally many plus and minus signs is $B_n=4^{-n}\binom{2n}{n}$. I choose two words independently, so the fraction for which both balance is $B_n^2$. At nonunit multiplier-one level $n$, the four recovered parameters $L$ share a radius $R_n$. I number the quartets from $n=1$ in increasing positive characteristic level. Since $R_n\sim2\pi n$ and $B_n^2\sim1/(\pi n)$, the weighted radius tends to $2$. Dividing by $2$ defines my normalized factor $C_n$. [Quartet radii and balanced sign counts](../../archive/2026-11-16-super-zeta-v001/research/binomial-normalization.md)

$`\displaystyle C_n=\frac{R_n B_n^2}{2}=\frac{R_n}{2\pi n}\,D_n, \qquad D_n=\pi n B_n^2.`$

The count also occurs in the Dottie map. I select four inverse branches of the two-stage return at the Dottie fold and assign them the four unit directions on a square lattice. A pair of signs gives one direction at each step. A walk of $2n$ steps returns to the origin exactly when both sign histories balance. Thus among the marked points fixed by $2n$ scalar returns on those four branches, the fraction with zero total displacement is $B_n^2$. This word uses $4n$ individual exponential stages. I chose the four branches, their directions, their equal weights and the pairing of word length $2n$ with quartet level $n$. The tower from the cap follows its prescribed alternating stages. [Four branches and the exact count, eqs. (5) and (15)–(17)](../../archive/2026-11-16-super-zeta-v001/research/balanced-charge-operators.md)

The leading Stirling factors in $(2n)!/(n!)^2$ cancel against the leading radial growth in $C_n$. To retain the factorial error, I write $S_n=\sqrt{2\pi n}(n/e)^n$ for Stirling's leading approximation and $\rho_n=\log(n!/S_n)$ for its logarithmic remainder. Substitution in $D_n$ leaves an exact combination of these remainders.

$`\displaystyle \begin{aligned} I(x)&=\int_0^\infty e^{-xt}\frac{\tanh(t/4)}{t}\,dt,\qquad x>0,\\ \log D_n&=2\rho_{2n}-4\rho_n=-I(n),\\ \log C_n&=\log\frac{R_n}{2\pi n}-I(n). \end{aligned}`$

For real $x>0$, $-I(x)$ is the logarithm of $x\Gamma(x+1/2)^2/\Gamma(x+1)^2$. The half-integer cosine spectrum used in the reconstruction of $\zeta(2s)$ also gives the partial fractions of $\tanh(t/4)/t$. A finite expansion of those fractions bounds the remainder by the first omitted term. Keeping the leading term gives

$`\displaystyle 0\le\log D_n+\frac{1}{4n}\le\frac{1}{96n^3},\qquad n\ge1.`$

At level 10 the estimate for $\log D_{10}$ is $-0.025$, with an error of at most $0.00001042$. I measure the displacement of the effective level $\Lambda_n=nC_n$ from its integer label by $\delta_n=n-\Lambda_n$. My quartet equations give $R_n-2\pi n\to0$, so the radial factor contributes at smaller order than $1/n$. The factorial term leaves a displacement of a quarter of the unit spacing in the limit. [Exact correction and all-order bound](../../archive/2026-11-18-stirling-correction-v001/README.md#the-exact-correction) · [Radial scale and quarter limit in Lean](../../lean/SuperZeta/QuartetRadius.lean) · [DLMF, Stirling's series](https://dlmf.nist.gov/5.11)

$`\displaystyle \Lambda_n=n-\frac14+o(1),\qquad \delta_n\longrightarrow\frac14 .`$

</details>

### The Hurwitz value changes sign between levels 28 and 29

The quartet radii change the sign of a finite-level test. At level 28 the Hurwitz value $\zeta(-1,1-\delta_n)$ is negative. At level 29 it is positive and stays positive thereafter.

![Hurwitz values at the first fifty quartet and grid levels, with a second plot enlarging the quartet sign change between levels 28 and 29.](../figures/proof-hurwitz-crossing.png)

<a name="fig-14"></a>**Fig. 14. The Hurwitz sign change between quartet levels 28 and 29.** On the left I plot $\zeta(-1,1-\delta_n)$ at the first 50 levels. Filled teal points use the measured quartet radius $R_n$. Open rust circles replace that radius by $2\pi n$ and keep the same balanced-sign weight. The right panel enlarges the measured values where they cross zero. Both displacements tend to $1/4$, but the grid keeps a positive Hurwitz value at every level. [Grid formula and the two level enclosures](../../archive/2026-11-18-quartet-grid-comparison-v001/README.md)

<details>
<summary>The sign test for the quartet radii and the comparison grid</summary>

Replacing $R_n$ by $2\pi n$ gives a positive value at every level, even though both sequences of displacements tend to $1/4$. To see where the signs separate, I evaluate the Hurwitz zeta for a unit-spaced sequence starting at $1-\delta$.

$`\displaystyle H(\delta)=\zeta(-1,1-\delta)=-\frac1{12}+\frac{\delta}{2}-\frac{\delta^2}{2}, \qquad \delta_c=\frac{1-1/\sqrt3}{2}=0.2113248654\ldots .`$

On $0<\delta<1/4$ the function is increasing and its sign changes at $\delta_c$. The actual displacements are about $0.211094$ at level 28 and $0.211856$ at level 29. I checked the first 127 levels with directed arithmetic and proved the uniform lower bound $\delta_n>0.22591304428$ from level 128 onward. Thus $H(\delta_n)$ is negative through level 28 and positive at every later level. The four marked members of each quartet give the same value because they share $R_n$. [Quarter-shift proof and directed prefix](../../archive/2026-11-18-lean-foundations-v001/notes/quarter-shift.md#1-global-discrete-theorem) · [Hurwitz special value](https://dlmf.nist.gov/25.11.E14)

The grid displacement $\delta_n^{\mathrm{grid}}=n(1-D_n)$ starts at $1-\pi/4\approx0.214602$, above the threshold, and increases to $1/4$. The exact difference $\delta_n^{\mathrm{grid}}-\delta_n=D_n(R_n-2\pi n)/(2\pi)$ isolates the radius correction that makes the finite crossing possible. The corrected independent audit reproduced the crossing, and Lean verifies that the grid stays above the threshold at every positive integer level. [Comparison, proof and corrected notebook](../../archive/2026-11-18-quartet-grid-comparison-v001/README.md) · [Quartet-radius theorem](../../lean/SuperZeta/QuartetRadius.lean) · [Grid threshold in Lean](../../lean/SuperZeta/Barnes.lean#L196-L224)

</details>

<div><a name="recovering-the-error-on-one-factorial"></a></div>

### Recovering the error on one factorial

For the single factorial $n!$, the logarithmic error in Stirling’s formula is $\rho_n=\log(n! /[\sqrt{2\pi n}(n/e)^n])$. The integral $I$ in my balanced-word weight gives the recurrence $\rho_n=I(n)/4+\rho_{2n}/2$.

<details>
<summary>The integral identity and its remainder bounds</summary>

Iterating at $n,2n,4n,\ldots$ recovers the full error, because the final term tends to zero by Stirling’s formula.

$`\displaystyle \rho_n=\frac14\sum_{j=0}^{\infty}2^{-j}I(2^j n), \qquad n!=\sqrt{2\pi n}\left(\frac ne\right)^n e^{\rho_n}.`$

Since $0\le I(x)\le1/(4x)$, stopping after the first $k$ terms leaves at most $4^{-k}/(12n)$ in the logarithm of the factorial ratio. For $10!$ the leading expression gives about $3{,}598{,}695.62$. The exact remainder multiplies it by about $1.0083653591$, giving $3{,}628{,}800$. This is the Stirling remainder in Binet's formula, recovered here by doubling the kernel of the balanced histories. [Binet's formula, DLMF 5.9.10₂](https://dlmf.nist.gov/5.9.E10_2) · [Exact factorial identity and kernel in Lean](../../lean/SuperZeta/StirlingCorrection.lean)

I can also evaluate the correction as one definite integral. In each $I(2^j n)$, rescale the integration variable so that the exponential becomes $e^{-nt}$. Every rescaled kernel is nonnegative, so monotone convergence allows the sum inside the integral. The identity $\tanh x=2\coth(2x)-\coth x$ cancels adjacent terms. For $t>0$ the first $k$ kernels give

~~~math
\frac14\sum_{j=0}^{k-1}2^{-j}\tanh\!\left(\frac{t}{2^{j+2}}\right)
=\frac12\coth\!\left(\frac t2\right)
 -\frac{1}{2^{k+1}}\coth\!\left(\frac{t}{2^{k+1}}\right).
~~~

Since $x\coth x\to1$ as $x\to0$, the last term on the right tends to $1/t$. This gives a formula for the factorial with no factorials in its integrand. The kernel multiplying $e^{-nt}$ tends to $1/12$ at $t=0$, and the exponential ensures convergence at infinity.

~~~math
n!=\sqrt{2\pi n}\left(\frac ne\right)^n
\exp\!\left[\int_0^\infty e^{-nt}
\left(\frac12\coth\frac t2-\frac1t\right)\frac{dt}{t}\right],
\qquad n\ge1 .
~~~

The Lean theorem gives the exact factorial in the doubled-index series. The cancellation above identifies that series with Binet’s single integral, using $\tfrac12\coth(t/2)=\tfrac12+1/(e^t-1)$. [Doubled-index factorial equality in Lean](../../lean/SuperZeta/StirlingCorrection.lean#L355) · [Binet’s integral](https://dlmf.nist.gov/5.9.E10_2)

For $10!$, I used $k=12$ and bounded the logarithmic tail by $1/(120\cdot4^{12})$. To evaluate each $I(x)$ without using any factorials, I substituted $u=xt$. I enclosed $e^{-u}\tanh(u/(4x))/u$ with 160-bit ball quadrature on the three intervals with endpoints $2^{-40},1,16,96$. The positive pieces below and above those cutoffs together contribute at most $(2^{-40}+e^{-96})/(4x)$ to $I(x)$, since $\tanh y\le y$ for $y\ge0$. Exponentiating the bounded sum and multiplying by Stirling’s factor gave $3{,}628{,}799.9981<10!<3{,}628{,}800.0001$ after outward rounding. The interval contains exactly one integer.

</details>

<div><a name="where-the-correction-enters-the-level-zeta"></a></div>

### The level zeta has value −1/4 at zero

The zeta function of the levels $\Lambda_n=nC_n$ has continued value $Z_\Lambda(0)=-1/4$.

<details>
<summary>Continuing the level zeta to zero</summary>

To compute it I introduce $\mathfrak Z(s,\nu)=\sum_{n\ge1}n^{-s}C_n^\nu$ and set $\nu=-s$, which gives $Z_\Lambda(s)=\sum_{n\ge1}\Lambda_n^{-s}$ for $\Re s>1$. The first term of $\log C_n$ contributes $-(\nu/4)\zeta(s+1)$ alongside $\zeta(s)$. The radial correction and the higher powers give a holomorphic remainder near $s=0$ that vanishes there on $\nu=-s$. Since $\zeta(s+1)$ has residue one at zero, $(s/4)\zeta(s+1)$ contributes $1/4$. Adding $\zeta(0)=-1/2$ gives the stated value. [Derivation near zero](../../archive/2026-11-18-stirling-correction-v001/README.md#the-correction-in-the-zeta-series) · [Continuation and value in Lean](../../lean/SuperZeta/DeformedZeta.lean) · [DLMF, zeta at zero](https://dlmf.nist.gov/25.6)

</details>

<div><a name="what-the-barnesdottie-constant-measures"></a></div>

### The Barnes–Dottie limit of the normalized product

Multiplying the first $N$ normalized quartet factors gives a product that decays like $N^{-1/4}$.

![The normalized products approach the Barnes–Dottie limit through five cutoffs up to 1,024](../figures/proof-barnes.png)

<a name="fig-15"></a>**Fig. 15. The normalized product and its Barnes–Dottie limit.** I multiply the product of the first $N$ quartet factors by $N^{1/4}$ to remove its leading decay. The five teal points use cutoffs from 16 to 1,024. The dashed rust line is the independently derived limit $e^{\sin(d)/2}/G(3/2)^2=1.225001707314\ldots$, which retains the contribution of the quartet radii in the numerator and the balanced-sign factorial weights in the denominator. [Five product measurements and exact limit](../../archive/2026-11-16-super-zeta-v001/computations/binomial-normalization-results.json)

<details>
<summary>The normalized product and its limiting constant</summary>

In its logarithm each level contributes $-1/(4n)$ to leading order, and their sum is $-(\log N)/4$ up to a finite offset. Multiplication by $N^{1/4}$ exposes the constant left by all the radii and factorial weights together.

$`\displaystyle \lim_{N\to\infty} N^{1/4}\prod_{n=1}^N C_n =\frac{e^{\sin(d)/2}}{G(3/2)^2} =1.2250017073142016853\ldots .`$

The product of the radial factors $R_n/(2\pi n)$ is exactly $e^{\sin(d)/2}$, where $d=\cos d$ is the Dottie number from the fold. I combine the factorial factors $D_n$ with the Barnes recurrence $G(z+1)=\Gamma(z)G(z)$ and $G(1)=1$. The asymptotic formula for $G$ as $N$ grows then gives $N^{1/4}\prod_{n=1}^N D_n\to1/G(3/2)^2$. [Exact radial product](../../archive/2026-11-16-super-zeta-v001/sources/foundation/radial-product-trace-theorem.md#2-the-same-trace-isolates-the-convergent-radial-product) · [Barnes product, eqs. (1)–(5)](../../archive/2026-11-16-super-zeta-v001/research/binomial-normalization.md#1-the-exact-global-normalization) · [DLMF, Barnes G-function](https://dlmf.nist.gov/5.17)

</details>

<div><a name="research-impact"></a><a name="conclusions"></a></div>

<div><a name="read-consequences" id="user-content-read-consequences"></a></div>

## Consequences for the ordered return, the factorial and the zero counts

Keeping the stage order lets me recover individual exponents on a period-640 orbit. Counting balanced words gives the factorial factor attached to each quartet radius. For the Riemann test, the finite orbit supplies a height and the zero count at that height comes from a contour integral. Each conclusion below identifies the calculation that gives it.

<details>
<summary>Four consequences and their proofs</summary>

- **Each rooted sign word gives a distinct map at fixed $L\ne0$.** In the free associative ring on the two signs, multiplication joins words. The number of plus signs minus the number of minus signs adds under concatenation, so the balanced words span its degree-zero subring. Counting two balanced words independently gives the $B_n^2$ in §5. [Finite-word theorem and the six four-stage endpoints](#user-content-read-sign-words) · [Balanced words and their ring](../../archive/2026-11-16-super-zeta-v001/research/ordered-signed-histories.md#1-the-operators-retain-every-arrangement)
- **Two measurements recover the orientation of the period-640 return.** Their reciprocals determine the real and imaginary parts of the normalized multiplier. On the centerline interval where its angle increases strictly with the parameter, I can run the calculation backward to recover the parameter, then iterate from the cap to recover the marked orbit. [Two spectral measurements and the centerline inverse](#user-content-read-period-640)
- **The factorial error can be evaluated at each level.** The exact integral for $\log D_n$ isolates the factorial contribution, and the ratio $D_{n+1}/D_n=1+1/(4n(n+1))$ carries it from one level to the next. The same integral yields the remainder on a single $n!$. Lean checks that identity and the bounds after truncating the combined expansion at any order. [Adjacent-level phase calculation](../../archive/2026-11-18-stirling-correction-v001/README.md#effect-on-phase-at-the-dottie-height) · [Single-factorial identity](../../lean/SuperZeta/StirlingCorrection.lean) · [All-order bounds](../../lean/SuperZeta/StirlingExpansion.lean)
- **The orbit fixes a height at which the zero count can be decided.** Once the marked lap sets $T_D$, I count zeros around $T_D$, $2T_D$ and $3T_D$. In each rectangle the count with multiplicity equals the number of disjoint critical-line sign changes. That equality places every zero there on the line and gives each one multiplicity one. [Height rule and certified counts](#user-content-read-zero-counts)

</details>

<div><a name="preprints-and-reproduction"></a></div>

<div><a name="read-preprints" id="user-content-read-preprints"></a></div>

## Preprints and reproduction

My first preprint defines the reciprocal tower, its sign words and the complex fixed pairs. The Dottie preprint follows the cap from the fold into the finite-period groups. Both manuscripts are available below as PDFs and editable TeX. The archive links lead to the computations, and the commands reproduce the archive and Lean checks.

| My preprint | Where to start |
| --- | --- |
| [*Reciprocal Tetration in the Logarithmic Lift* (PDF)](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.pdf) · [Editable TeX](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex) | The two ordered stages, their fixed pairs, sign words, and the Dottie and Sirius orbit records. |
| [*The Dottie Parabolic Fold and the Marked Spire* (PDF)](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.pdf) · [Editable TeX](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex) | The local fold, its even and odd returns, finite periods, and the hypotheses connecting them to the limiting horn maps. |

<details>
<summary>Archived calculations and independent reproduction</summary>

The archive contains the derivations and computations in the order I developed them. [Foundations and rational traces](../../archive/2026-11-16-super-zeta-v001/README.md) · [Ordered return](../../archive/2026-11-17-quartet-return-recursion-v001/README.md) · [Off-line zero tests](../../archive/2026-11-17-offcenter-superzeta-v001/README.md) · [Distance bounds](../../archive/2026-11-18-superzeta-distance-v001/README.md) · [Newton steps](../../archive/2026-11-17-quartet-angle-v001/README.md) · [Binary valuation law](../../archive/2026-11-18-binary-law-v001/README.md)

I keep the original figures alongside the measured records. These are the versions cited before I redrew the plots and moved the explanations into this paper’s captions.

- For the original quadratic and reciprocal tower, see the [quartic ovals (Fig. 1)](../../archive/2026-11-18-quartic-ovals-v001/quartic-ovals.png), [quadratic approximation (Fig. 2)](../../archive/2026-11-18-research-figures-v001/pi-hat.png) and [Dottie spire (Fig. 3)](../../archive/2026-11-18-research-figures-v001/dottie-spire.png).
- For the moving Hurwitz zeros, see the [successor paths (Fig. 6)](../../archive/2026-11-19-zero-transport-v001/Dottie-Forward-Iteration/successor-paths.png), [three passes (Fig. 7)](../../archive/2026-11-19-sixth-passes-v001/preview.png), [nearby trajectories (Fig. 8)](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/complex_turn.png), [relative displacement (Fig. 9)](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/complex_offset.png) and [two destination maps (Fig. 10)](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/basins.png).
- For the factorial normalization, see the [partial products and the Barnes–Dottie limit (Fig. 15)](../../archive/2026-11-16-super-zeta-v001/figures/barnes-dottie-normalization.png).

**I invite independent reproduction** of the determinant product and Mellin integral on their specified logarithm branch, the contour winding and both endpoint signs in every Hardy bracket, and the passage from a finite cap orbit to a particular horn in a common phase coordinate. The first Dottie window contained two line zeros and its matched grid window contained three. The separate height-selection experiment asks how often an orbit-selected window improves on its controls. [Reproduction guide](../../archive/2026-11-18-spectral-reproduction-v001/README.md) · [Matched experiment](../../archive/2026-11-17-dottie-grid-match-v001/README.md)

</details>

<details>
<summary>Commands for archive, Lean and numerical verification</summary>

From the repository root, the first command checks archive hashes. The second builds the pinned Lean project and audits theorem dependencies. The third regenerates the Hurwitz speed and two-input spectral reports in temporary storage, compares their bytes with the archive, and checks the precision table in §3.13. For that numerical replay I used Python 3.12.11 with python-flint 0.9.0 (FLINT 3.6.0). The contour and global-count checks in §4 use different algorithms in FLINT. I would welcome a reproduction with a separately implemented zeta evaluator. [Lean setup](../../lean/README.md) · [Archive preservation](../../PRESERVATION.md) · [Numerical replay](../../tools/replay_two_input_results.py)

~~~sh
python tools/verify_archive.py
python tools/check_lean.py --fetch-cache
python -B tools/replay_two_input_results.py
~~~

</details>

<div><a name="zero-transport-questions"></a><a name="questions-in-the-order-i-asked-them"></a></div>

<div><a name="read-questions" id="user-content-read-questions"></a></div>

## Research questions in chronological order

Following a Hurwitz zero through one turn gave me successive Riemann zeros, then an elementary zero, then a jump to the seventh. Which starting addresses determine those different landings is still open. I keep the original order and link each crossed-out question to its calculation.

<details>
<summary>Questions 1–9. Hurwitz paths and their endpoints</summary>

1. ~~Can I reuse the previous endpoint to reach the second Riemann zero?~~ Yes. The seed $4\pi i/\log 2$ reached $\rho_2$. [Prediction and certificate](../../archive/2026-11-19-zero-transport-v001/Dottie-Second-Zero/REPLAY.txt)
2. ~~Does the second zero itself lead directly to the third?~~ Yes, in one turn. [Path and ordinal count](../../archive/2026-11-19-zero-transport-v001/Dottie-Third-Zero/REPLAY.txt)
3. ~~Starting at the third zero, does repeating the turn keep finding consecutive zeros?~~ The first turn reached the fourth. The next two reached an elementary address and then the seventh, triggering the frozen stopping rule. [Prospective record](../../archive/2026-11-19-zero-transport-v001/Dottie-Forward-Iteration/results.json)
4. ~~If I turn back from the seventh zero, do I recover the same intermediate address?~~ Yes. Reversing the simple branch recovered $8\pi i/\log 2$. [Reverse certificate](../../archive/2026-11-19-zero-transport-v001/Dottie-Transport-Reversibility/reverse-identification.json)
5. ~~Could the two missed zeros be the critical-line crossings on the blue path leaving the fourth zero?~~ That path has three interior crossings. Ordinary zeta is nonzero at each. [Angles in multiples of π](../../archive/2026-11-19-zero-transport-v001/Dottie-Transport-Reversibility/rotations.md)
6. ~~Which starting addresses lead to the fifth and sixth zeros on this turn?~~ The base-three addresses with indices five and six. I identified them backward, then checked both from the exact seeds in the forward direction. [Retrospective inverse study](../../archive/2026-11-19-zero-transport-v001/Dottie-Transport-Reversibility/README.md)
7. **Open.** Given only a starting address, which features of the moving zero determine its endpoint's family and, when it lands on a Riemann zero, its ordinal?
8. **Open.** Which positive-height Riemann zeros have a unique regular predecessor on the extra base-three lattice, and can I characterize that set before computing their paths?
9. ~~Do earlier studies contain these same paths?~~ Yes. The five trajectories in Figures 2–4 of the 2007 paper include four successive links of my early route and one further elementary connection. [Figure-by-figure comparison](../../archive/2026-11-19-zero-transport-v001/Dottie-Transport-Reversibility/PRIOR-WORK.md)

</details>

<details>
<summary>Questions 10–19. Folds, crossings and two return angles</summary>

10. ~~What makes the sixth path pass the same height three times?~~ Its velocity turns through the horizontal twice. The two folds enclose a whole band of repeatedly visited heights. [Three passes, two folds](../../archive/2026-11-19-sixth-passes-v001/README.md)
11. **Open.** Can I use the two Hurwitz shifts to bound the total turning of other branches before tracing their zeros?
12. ~~Can one labeled Hurwitz term recover which way I leave the sixth branch's crossing when the position, angle and both traces are hidden?~~ Each of the two readings isolates its own visit. The calibrated angle then recovers its Dottie orbit. [Blinded inverse](../../archive/2026-11-19-single-term-inverse-v001/README.md#the-experiment)
13. ~~Does a single term distinguish every visit on that sweep?~~ It has one transverse double point. Adding the position separates that last pair. [Full-sweep comparison](../../archive/2026-11-19-single-term-inverse-v001/chart.json)
14. **Open.** On which other positive-height Hurwitz branches does the pair of the zero position and one labeled summand distinguish every visit?
15. ~~Does one estimated acceleration near the last trough explain the full rise to the sixth zero?~~ It accounts for $`27.23\%`$. Updating the derivatives gives a much more accurate endpoint. [Masked forecast](../../archive/2026-11-19-dottie-plane-atlas-v001/landing/README.md)
16. ~~What happens to neighboring points as that zero moves?~~ At two certified starting points one neighborhood shrinks and the other expands, with length factors $0.28613$ and $8.0752$. [Level transport](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/plane_notes.md)
17. ~~Can two logarithms of the same Dottie multiplier send the same starting point to different zeros?~~ Yes. All seeds in a disk around $37i$ go to different named zeros under the principal and ordered logarithms of the multiplier. [Basin certificate](../../archive/2026-11-19-dottie-plane-atlas-v001/atlas/basin_certificate.json)
18. ~~Do the two publicly chosen next triadic seeds meet the forecast rule for the last $\pi/1440$ radians?~~ Both landed in their forecast boxes and in the forecast families. [Results and fixed protocol](../../archive/2026-11-19-dottie-plane-atlas-v001/holdout/README.md)
19. **Open.** Which other marked orbits and starting domains admit a comparable description of the branch values that separate their destinations?

</details>

<details>
<summary>Questions 20–24. Angular speed and spectral reconstruction</summary>

20. **Open for individual zeros.** At a simple Riemann zero $\rho$, can $\zeta(\rho)=0$ sharpen the pointwise bound on $\lvert L(1+\rho,\chi_{-3})/(1-3^{-\rho})\rvert$ at every height? [Pointwise estimate](../../archive/2026-11-20-liu-angular-velocity-v001/README.md#from-a-bound-on-position-to-a-bound-on-speed)
21. ~~Can I estimate the mean square over simple zeros in a short interval and compute it in my three Dottie windows?~~ I have certified values in all three. At almost all centers of shrinking windows containing simple zeros, their mean squared speed is approximated by $`\lvert G(1/2+it)\rvert^2`$ at the center height $t$. [Theorem and enclosures](../../archive/2026-11-20-hurwitz-speed-mean-square-v001/README.md)
22. **Open.** If I count only simple zeros up to height $T$, does their mean squared speed still tend to $`13\zeta(3)/\pi^2`$, and does it retain the same prime-power correction? [Bounds for the simple-zero average](../../archive/2026-11-20-hurwitz-speed-mean-square-v001/README.md#a-cumulative-bound-when-only-simple-zeros-are-counted)
23. ~~Can two complex exponents determine the entire squared quartet spectrum?~~ Exact data across one plane of fixed real part determine every squared root with multiplicity. In the finite calculation, five readings across $r=16,17$ recover the first conjugate pair. [Full-plane proof and five-reading inverse](../../archive/2026-11-20-hurwitz-speed-mean-square-v001/two-input-spectrum.md)
24. **Open.** Given a fixed precision for the readings, how many consecutive quartet levels can be recovered with disjoint certified enclosures? The first level is the finite test case. [Five input intervals](../../archive/2026-11-20-hurwitz-speed-mean-square-v001/two-inputs.json)

</details>

<div><a name="gaussian-disk-remainder"></a></div>

25. **Open.** At cutoff $N=262144$, the real part of the smoothed finite sum lies below $-7.6098\times10^{-29}$ everywhere on the right circle. Can the signed Gaussian prime-ideal coefficients bound the real part of the omitted contribution uniformly above by a number smaller than $7.6098\times10^{-29}$, in the same scaling? This would keep the full boundary strictly in the left half-plane and clear both reflected disks. At this cutoff the bound on the absolute value of the omitted contribution is $2.312\times10^{-17}$. [Boundary calculation and replay](../../archive/2026-11-20-gaussian-reflected-disks-v001/README.md#what-the-circle-calculation-resolves) · [Sufficient condition in Lean](../../lean/SuperZeta/GaussianDiskCount.lean)

26. ~~Can the measured quartic signs leave a gap in spiral phase on an entire circle as I increase the cutoff?~~ On the outer circle of radius $31/2048$, the finite sum missed the chosen phase of $3.9$ radians by more than $0.91$ radians at each of 193 cutoffs. The same test on the reflected circle crossed that phase twice per cutoff. [Measured phases and interval replay](../../archive/2026-11-20-gaussian-circle-phases-v001/README.md)
27. **Open.** Does the omitted signed contribution preserve a missing phase on the full, nonvanishing Gaussian boundary? A positive answer on the outer circle would give winding zero and clear both disks by reflection. [Remainder estimate at the final cutoff](../../archive/2026-11-20-gaussian-circle-phases-v001/README.md#why-the-two-crossings-preserve-the-zero-count)

<div><a name="credits"></a></div>

<div><a name="read-credits" id="user-content-read-credits"></a></div>

## Credits

I use Baker and Rippon’s half-step to locate the fold, the symmetric Hurwitz family studied by McPhedran, Botten and Nicorovici to follow zeros as the Hurwitz shift varies, and the zero-free bounds of OpenAI and Liu for comparison with the Riemann factor. The references below identify the theorem, formula or computation I used from each source.

<details>
<summary>Authors, formulas and published sources</summary>

- **Ross C. McPhedran, Lindsay C. Botten and Nicolae-Alexandru P. Nicorovici** traced zeros of the same symmetrized Hurwitz function. Their equation (3.1) gives the motion of a simple zero, and (3.4) gives the specialization at thirds. Their companion paper with **I. J. Zucker** gives both mod-three identities in (6.3) and (6.5). **Hans Frisk and Serge de Gosson**, and later **Ramūnas Garunkštis and Jörn Steuding**, studied trajectories and endpoint classifications for the single Hurwitz function. I give formula and figure references beside the numerical comparisons. [McPhedran, Botten and Nicorovici (2007), §3](https://doi.org/10.1098/rspa.2006.1763) · [Companion paper, §6](https://doi.org/10.1098/rspa.2006.1762) · [Frisk and de Gosson (2001), §2](https://arxiv.org/abs/math-ph/0102007) · [Garunkštis and Steuding (2011), §2](https://journals.vilniustech.lt/index.php/MMA/article/view/5510) · [Detailed comparison](../../archive/2026-11-19-zero-transport-v001/Dottie-Transport-Reversibility/PRIOR-WORK.md)

- **Michael Creutz and Robert M. Sternheimer** and **I. N. Baker and P. J. Rippon** provide the earlier work on alternating towers. Baker and Rippon give the centerline return, boundary, multiplier and antiholomorphic half-step I use. **Lasse Rempe and Dierk Schleicher** give the complex exponential parameter-space framework. **Robert Corless and coauthors** give the Lambert $W$ branches used in my fixed-pair atlas. [Creutz and Sternheimer](https://www.fq.math.ca/Scanned/19-4/creutz.pdf) · [Baker and Rippon, Theorem 8.1 and eqs. (12)–(13)](https://doi.org/10.1080/17476938908814364) · [Rempe and Schleicher](https://doi.org/10.1017/CBO9780511735233.014) · [Corless et al.](https://doi.org/10.1007/BF02124750)
- **Samuel R. Kaplan** documented the fixed point of cosine as the Dottie number. [*The Dottie Number*](https://doi.org/10.1080/0025570X.2007.11953455)
- **David R. Stoutemyer** supplied the inverse spherical Bessel framework, and **Riccardo Borghi** supplied the positive Stieltjes representation of the Bessel solution of Kepler’s equation. I used their 2024 results in the companion work on branches and approximation. [Stoutemyer’s paper](https://doi.org/10.5206/mt.v4i2.16787) · [Borghi’s paper](https://www.mdpi.com/2227-7390/12/1/154) · [Companion notes](../../archive/2026-11-18-lean-foundations-v001/README.md#results-and-their-evidence)
- **Jean Écalle and Sergei Voronin** provide the parabolic classification used for the return coordinates. I use **Dudko and Sauzin** for the analytic properties of Fatou coordinates, **Godin and Rousseau** for the antiholomorphic classification, and **Kuehn** for saddle-node scaling. [Écalle and Voronin in the preprint bibliography](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/references.bib#L36-L58) · [Dudko and Sauzin](https://doi.org/10.1016/j.crma.2013.12.005) · [Godin and Rousseau](https://doi.org/10.1017/etds.2021.98) · [Kuehn](https://doi.org/10.1088/1751-8113/42/4/045101)
- **Tom Fisher** supplied the binary-quartic framework used in the arithmetic notes. I use **Folkmar Bornemann’s** projection methods for the spectral determinant and **André Voros’s** framework for zeta functions over zero sets. [Fisher](https://people.maths.bris.ac.uk/~jb12407/ANTS-XV/papers/ANTS-XV_fisher.pdf) · [Bornemann](https://arxiv.org/abs/0804.2543) · [Voros](https://arxiv.org/abs/1403.4558)
- **H. J. Hupkes** gives the earlier derivative and midpoint formulation for mixed-type functional differential equations. The endpoint choice above identifies the shared characteristic equation. [Hupkes, chapter 2](https://math.leidenuniv.nl/scripties/PhdHupkes.pdf)
- **Baiying Liu** obtains the zero-free half-plane $\Re w>B_{\ast}$ from joint moment estimates for unitary Hecke $L$-functions. I use the Riemann case in §3.11. **Joseph Bebel** gives a separate Lean proof at the same algebraic endpoint for every Dirichlet character, building on **TheSil**’s bounds. Modulus one supplies the Riemann theorem used by my local Lean transfer. [Liu, *Joint marked moments and optimized zero-free half-planes for unitary Hecke L-functions*, Theorems 1.1 and 7.2](https://hexagonmath.org/pdf/2611.00421v1) · [TheSil’s bound](https://github.com/GTimG/QuasiRiemannTracker/pull/137) · [Bebel’s exact endpoint](https://github.com/GTimG/QuasiRiemannTracker/pull/143) · [Verification and reproduction](../../archive/2026-11-20-liu-angular-velocity-v001/README.md#verification-and-reproduction)
- **OpenAI** proved the 7/8ths zero-free theorem I use at the first Dottie height. The counts use the real $Z$ function of **G. H. Hardy**, and the cross-check uses the procedures credited in FLINT’s zero-counting documentation. [*The Quasi-Riemann Hypothesis*, Theorem 1.1](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) · [DLMF, Hardy’s Z function](https://dlmf.nist.gov/25.10.E1) · [FLINT’s algorithms and sources](https://flintlib.org/doc/algorithms/special-functions/zeta-zeros.html)
- I used **Fredrik Johansson’s** ball arithmetic and **Siegfried Rump’s** verification methods for the numerical certificates. I use **Lean and mathlib** for the formal proofs, **FLINT** for directed interval arithmetic, and **PARI/GP** for the arithmetic descent. The **NIST Digital Library of Mathematical Functions** supplies the classical formulas cited at the Mellin, zeta and Barnes steps. [Johansson](https://doi.org/10.1109/TC.2017.2690633) · [Rump](https://doi.org/10.1017/S096249291000005X) · [mathlib](https://github.com/leanprover-community/mathlib4) · [FLINT](https://flintlib.org/) · [PARI/GP](https://pari.math.u-bordeaux.fr/)

The preprint bibliographies give the wider references for alternating towers, parabolic dynamics and validated numerics. I keep a separate source map for the formulas in the super zeta notes. [Reciprocal tetration bibliography](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/references.bib) · [Dottie spire bibliography](../../archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/references.bib) · [Super zeta source map](../../archive/2026-11-16-super-zeta-v001/source-map.md#published-inputs-and-their-actual-use)

</details>
