# The Super Zeta Function

I wanted to see how closely I could approximate $\pi$ using $e$ and six integers. When I solved the quadratic, I found a curve with two real ovals and a simple rule that swaps its two roots. The same reciprocal expression showed up in the tower I was studying. It gave me a way to find the complex roots of the Dottie fold equation. Summing inverse powers of those roots led me to my super zeta function.

[Quadratic and real ovals](#the-quadratic-and-the-genus-one-curve) · [Reciprocal tetration and the Dottie spire](#reciprocal-tetration) · [The super zeta](#building-the-super-zeta) · [The three certified intervals](#a-local-strengthening-of-the-seven-eighths-theorem) · [Preprints and proofs](#preprints-and-reproduction) · [Credits](#credits)

<a name="from-the-original-meme-to-the-dottie-spire"></a>

## The quadratic and the genus-one curve

My six integers are the coefficients of these two polynomials.

$$
\begin{aligned}
N(x)&=465x^2-183x-659,\\
D(x)&=155x^2+396x-936.
\end{aligned}
$$

I set $T(y)=(1+y)(2+y)/(y^2+y-1)$ and equated it to $N(x)/D(x)$. Clearing the denominators gave me a quadratic in $y$. Completing the square is what made the geometry visible.

$$
\begin{aligned}
0&=(N-D)y^2+(N-3D)y-N-2D,\\
Y&=2(N-D)y+N-3D,\\
Y^2&=(N-D)^2+4N^2\\
   &=961000x^4-1039740x^3-1810543x^2+644010x+1813853.
\end{aligned}
$$

The sum of squares stays positive for real inputs. Each graph closes through its own point at infinity, giving the **two real ovals** below. To see the genus, I looked for where the two values of $Y$ meet over $\mathbb C$. They meet at the four simple roots of the quartic. A double cover with four branch points has genus one by Riemann–Hurwitz, so the completed complex curve is a torus. [Exact geometry of the quartic](archive/2026-11-18-lean-foundations-v001/arithmetic/research/geometry.md)

![The upper and lower real branches close into two ovals, with the point at x=e marked on the upper branch](archive/2026-11-18-quartic-ovals-v001/quartic-ovals.png)

The branches are farthest apart in the left panel at $x\approx0.057794$ and closest at $x\approx1.400168$. The latter is close to the positive zero of $N(x)$, where the original quadratic attains its exact minimum root gap of one, with roots $-1$ and $-2$. [Plot coordinates and verified extrema](archive/2026-11-18-quartic-ovals-v001/README.md)

I checked solvability over the reals and over $\mathbb Q_p$ at every prime. The quartic passes all those local tests. The arithmetic descent rules out a rational point, making it a **counterexample to the Hasse principle**. [Local points in Lean](lean/SuperZeta/HasseCover.lean) · [Computer-assisted descent](archive/2026-11-18-lean-foundations-v001/arithmetic/research/hasse-obstruction.md)

### The point giving my approximation to π

To get my approximation, I put $x=e$ on the upper oval and convert back from $Y$ to $y$. That point gives the root $\widehat\pi$ of $T(y)=N(e)/D(e)$ near $\pi$.

$$
\widehat\pi=\frac{3D(e)-N(e)+Y(e)}{2\bigl(N(e)-D(e)\bigr)}
=3.14159265358979323837582331055\ldots
$$

The plot is centered at $(\pi,T(\pi))$, with both axes in units of $10^{-20}$. The horizontal error is $\pi-\widehat\pi\approx8.682007272725\times10^{-20}$. [Lean proof of the error bound](lean/SuperZeta/MemePrecision.lean)

![The intersection yielding pi-hat lies about 8.682 times 10 to the minus 20 below pi](archive/2026-11-18-research-figures-v001/pi-hat.png)

The part I carried into the tower was $p=2y+3$. In that coordinate my quadratic is $p-p^{-1}=4N/(N-D)$, and $p\mapsto-1/p$ swaps its two roots. [Reciprocal substitution in Lean](lean/SuperZeta/Meme.lean)

## Reciprocal tetration

I write $\operatorname{tet}(x)=x^x$ for the height-two tower. For a positive real base I use $L=\log x$. For a nonzero complex base I choose a logarithm $L$ with $x=e^L$, so $x^z=e^{Lz}$ throughout the iteration.

The pair $x^{x-a},x^{x+a}$ is a way to start thinking about two exponents at once. In my tower I alternate the bases $x$ and $x^{-1}$ and feed each output into the opposite stage. I start at $(1,1)$ and use the update

$$
F_L(P,Q)=\bigl(e^{LQ},e^{-LP}\bigr).
$$

With center $m=(Q-P)/2$ and half-difference $a=(Q+P)/2$, the updated pair is $(x^{m+a},x^{m-a})$. I keep the exponents $U=LQ$ and $V=-LP$ attached to their outputs so I can read back $Q=U/L$ and $P=-V/L$ when $L\ne0$. This lets me follow which stage a value came from. Two updates bring each phase back to itself as a map. The first return is $g_L(z)=e^{L e^{-Lz}}$ and the second is $g_{-L}$. My preprint calls the second phase $M$. [Reciprocal-tetration preprint](archive/2026-11-18-lean-foundations-v001/papers/foundations/main.pdf) · [The ordered return in Lean](lean/SuperZeta/Reciprocal.lean)

### The Dottie spire

I colored each parameter by the length of the cycle the orbit from $(1,1)$ appeared to settle into. The narrow stack of period groups is what I call the **Dottie spire**. Each group gives me a length for one lap, so I know how many times each exponential stage acts before the cycle repeats.

I used Baker and Rippon’s fixed-pair curve on the imaginary axis to locate the tip. In their parametrization, $L=iY(u)$ with

$$
Y(u)=u\sec u\,e^{-u\tan u},
\qquad
\frac{Y'(u)}{Y(u)}=\frac{\cos^2u-u^2}{u\cos^2u}.
$$

The two fixed branches meet at a stationary point with return multiplier one. On $0<u<\pi/2$ that point satisfies $u=\cos u$. This is how the Dottie number $d$ ended up locating the tip of my picture at $L_*=i e^{-\sin d}\approx0.509863605523013\,i$. [Baker and Rippon, eqs. (12)–(13)](https://doi.org/10.1080/17476938908814364) · [Dottie spire preprint, §2](archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.pdf) · [The fold in Lean](lean/SuperZeta/Dottie.lean)

![The Dottie spire with the parabolic fold marked and a Layer 4 close-up near the tip](archive/2026-11-18-research-figures-v001/dottie-spire.png)

Gray shows where the Layer 4 survey reached its limit with the period unresolved. The group I used for the zeta experiment came from a separate calculation. At two reflected points $L_\pm=\pm\eta+iy$ and their midpoint $L_0=iy$, I certified attraction to a cycle of period 320 under the two-step return, or 640 paired updates. The exact inputs are $\eta=4.749479070945369\times10^{-8}$ and $y=0.509892982511772$. [2540 × 1590 render and settings](archive/2026-11-18-research-figures-v001/README.md) · [384-bit period certificate](archive/2026-11-18-lean-foundations-v001/checks/dottie_slice.py)

<a name="the-spectral-zeta-and-the-critical-line"></a>

## Building the super zeta

Once I knew the fold was at multiplier one, I wanted to find the other fixed pairs with that multiplier. The multiplier is $UV$, so I can put $U=\alpha$ and $V=\alpha^{-1}$. The fixed equations give $\alpha^2 e^{\alpha-\alpha^{-1}}=-1$. Here the reciprocal difference from my quadratic is exactly the useful coordinate. With $2iu=\alpha-\alpha^{-1}$, the equation gives $\alpha e^{iu}=\pm i$ and then $u=\pm\cos u$.

The real roots are $\pm d$, and the other roots come in quartets $\{u_n,-u_n,\bar u_n,-\bar u_n\}$. Squaring merges each sign pair. In the variable $v=u^2$ the determinant is the entire function

$$
E(v)=\cos^2\sqrt v-v=1-2v+\frac{v^2}{3}-\frac{2v^3}{45}+\cdots.
$$

This is the step that gave me a zeta function. The zeros of $E$ are the squared values $d^2,u_n^2,\bar u_n^2$. I raise each to the power $-s$ using its principal logarithm and sum them.

$$
\mathcal Z(s;1)=d^{-2s}+\sum_{n\ge1}\bigl[(u_n^2)^{-s}+(\bar u_n^2)^{-s}\bigr],
\qquad \Re s>\frac12.
$$

Writing $E$ as a product over its roots ties this sum to the power series. For instance, the coefficient of $v$ is $-2$, which says the sum of the reciprocal roots is $\mathcal Z(1;1)=2$.

I got to Riemann zeta by comparing $E$ with the reference function $\cos^2\sqrt v$. Its double zeros are the squares of $(n+\tfrac12)\pi$. They give twice the reciprocal-power sum over odd positive integers with exponent $2s$, scaled by $(2/\pi)^{2s}$. The ratio of the two functions at $v=-t$ is $1+t/\cosh^2\sqrt t$. Integrating the logarithm of this ratio gives the correction $J$, which extends to an entire function. That leaves the exact identity

$$
F(s)=\mathcal Z(s;1)-J(s;1)=2\pi^{-2s}(2^{2s}-1)\zeta(2s).
$$

With $w=2s$, the prefactor is nonzero in $0<\Re w<1$. Each Riemann zero therefore corresponds to a zero of $F$ with the same multiplicity. The line $\Re w=1/2$ becomes $\Re s=1/4$, and its heights are halved as well. [Cosine roots and spectral derivation, eqs. (1)–(5) and (20)–(23)](archive/2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md) · [Lean root list and the Hadamard factorization hypothesis](archive/2026-11-18-quartet-levels-v001/README.md)

## A local strengthening of the seven-eighths theorem

### How the iteration gives the height

I used the certified period-320 lap at the spire to choose where to count. Each of the two marked exponential stages occurs 320 times per lap. The derivative divided by the output of $z\mapsto e^{\pm Lz}$ is $\pm L$, so comparing the product for one marked stage at a flank with its product at the midpoint gives the modulus ratio $(|L_\pm|/|L_0|)^{320}$.

I used the logarithm of that ratio as the phase scale. One winding gives a phase change of $2\pi$, which fixes the Riemann height

$$
T_D=\frac{2\pi}{160\log(1+(\eta/y)^2)}
=4{,}526{,}119{,}322{,}477.945393\ldots .
$$

I fixed the rule and the first window before evaluating zeta there. I also counted zeros in a window of the same width around the nearest multiple of $\pi$. That comparison interval contained three zeros, all on the critical line. [Height rule, winding and matched comparison](archive/2026-11-17-dottie-grid-match-v001/README.md)

### What the three windows tell me

I wanted to know whether the spire had pointed me to a sideways pair of zeros, at the same height and on opposite sides of the line. That takes a count over the whole window. A pair could sit between the heights I happened to sample.

Writing $w=\beta+it$, OpenAI’s seven-eighths theorem and the functional equation confine every nontrivial zero to $1/8\le\beta\le7/8$. That was enough to extend my first count to the full strip. The rectangle I had checked already covered the entire range they allow. I counted the full width directly for the windows at $2T_D$ and $3T_D$. [OpenAI, Theorem 1.1](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) · [Functional equation](https://dlmf.nist.gov/25.4)

| Interval in Riemann height $t$ | Simple zeros on $\beta=\tfrac{1}{2}$ | Off-critical-line zeros | Certificate |
| --- | ---: | ---: | --- |
| $\lvert t-T_D\rvert\lt\tfrac{1}{4}$ | 2 | 0 | [First height](archive/2026-11-17-dottie-local-strip-v001/README.md) |
| $\lvert t-2T_D\rvert\le\tfrac{1}{2}$ | 5 | 0 | [Second height](archive/2026-11-18-superzeta-distance-v001/README.md) |
| $\lvert t-3T_D\rvert\le\tfrac{1}{2}$ | 4 | 0 | [Third height](archive/2026-11-18-superzeta-distance-v001/README.md) |

I counted every zero inside each rectangle with the argument principle. Then I located zeros on the line by checking separate sign changes of Hardy’s $Z$-function. The two counts agreed in every window, so the eleven zeros on the line account for the entire total, with multiplicity one.

That tightens the seven-eighths bound to $\beta=1/2$ throughout those three intervals. In my super zeta coordinate the result is $\Re s=1/4$ over the corresponding halved height intervals. [Full-width counts and independent check](archive/2026-11-18-superzeta-distance-v001/README.md)

## The factorial correction

I also wanted to see what happens to the quartet radii from one level to the next. I used $B_n=4^{-n}\binom{2n}{n}$ to put the common radius $R_n$ on the scale $C_n=R_nB_n^2/2$. The factorials cancel in a way that lets me write the Stirling error exactly.

$$
\log C_n=\log\frac{R_n}{2\pi n}-\int_0^\infty e^{-nt}\frac{\tanh(t/4)}{t}\,dt.
$$

The integral contributes $-1/(4n)$ with a correction between $0$ and $1/(96n^3)$. That matters because a small term at each level accumulates over the whole spectrum. In $\sum_{n\ge1}n^{-s}C_n^\nu$ it gives $-(\nu/4)\zeta(s+1)$, and the zeta function of the levels $nC_n$ has regularized value $-1/4$ at zero. It also supplies the power $N^{1/4}$ in the normalized product below, whose limit is $e^{\sin(d)/2}/G(3/2)^2$ with the Barnes $G$-function. [Exact error and Lean proofs](archive/2026-11-18-stirling-correction-v001/README.md) · [Barnes product](archive/2026-11-16-super-zeta-v001/research/binomial-normalization.md)

![The normalized products approach the Barnes–Dottie limit through five cutoffs up to 1,024](archive/2026-11-16-super-zeta-v001/figures/barnes-dottie-normalization.png)

## Preprints and reproduction

My two working preprints are available as PDFs and editable TeX. They give the alternating tower, the fixed-point branches and the spire’s marked return structure.

- [Reciprocal Tetration in the Logarithmic Lift (PDF)](archive/2026-11-18-lean-foundations-v001/papers/foundations/main.pdf) · [TeX](archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex)
- [The Dottie Parabolic Fold and the Marked Spire (PDF)](archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.pdf) · [TeX](archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex)

I keep the spectral derivations, further experiments and exact checks in the dated archives. [Foundations and rational traces](archive/2026-11-16-super-zeta-v001/README.md) · [Ordered return](archive/2026-11-17-quartet-return-recursion-v001/README.md) · [Off-line zero tests](archive/2026-11-17-offcenter-superzeta-v001/README.md) · [Distance bounds](archive/2026-11-18-superzeta-distance-v001/README.md) · [Newton steps](archive/2026-11-17-quartet-angle-v001/README.md) · [Binary valuation law](archive/2026-11-18-binary-law-v001/README.md)

To check the archive and build the proofs, run these commands from the repository root. [Source inventory](archive/2026-11-18-lean-foundations-v001/README.md) · [Lean theorem index and setup](lean/README.md) · [Archive preservation](PRESERVATION.md)

~~~sh
python tools/verify_archive.py
python tools/check_lean.py --fetch-cache
~~~

## Credits

- **I. N. Baker and P. J. Rippon** established the alternating-conjugate return, its convergence boundary and the multiplier calculation. I used their parametrization to identify the Dottie value of the boundary exactly. [*Towers of Exponents and Other Composite Maps*, Theorem 8.1 and eqs. (12)–(13)](https://doi.org/10.1080/17476938908814364)
- **Samuel R. Kaplan** documented the fixed point of cosine as the Dottie number. [*The Dottie Number*](https://doi.org/10.1080/0025570X.2007.11953455)
- **David R. Stoutemyer** supplied the inverse spherical Bessel framework, and **Riccardo Borghi** supplied the positive Stieltjes representation of the Bessel solution of Kepler’s equation. I used their 2024 results in the companion work on branches and approximation. [Stoutemyer’s paper](https://doi.org/10.5206/mt.v4i2.16787) · [Borghi’s paper](https://www.mdpi.com/2227-7390/12/1/154) · [Companion notes](archive/2026-11-18-lean-foundations-v001/README.md#results-and-their-evidence)
- **Tom Fisher** supplied the binary-quartic framework used in the arithmetic notes. **Folkmar Bornemann** supplied the projection and determinant framework used in the spectral derivation. [Binary quartics and the Cassels–Tate pairing](https://people.maths.bris.ac.uk/~jb12407/ANTS-XV/papers/ANTS-XV_fisher.pdf) · [On the numerical evaluation of Fredholm determinants](https://arxiv.org/abs/0804.2543)
- **OpenAI** proved the seven-eighths zero-free theorem I use to extend the first contour certificate to the full critical strip at the Dottie height. [*The Quasi-Riemann Hypothesis*, Theorem 1.1](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf)
- I used the **NIST Digital Library of Mathematical Functions** for the Mellin formulas and the zeta functional equation. I use **Lean and mathlib** for the formal proofs, **FLINT** for directed interval arithmetic, and **PARI/GP** for the arithmetic descent. [DLMF §2.5](https://dlmf.nist.gov/2.5) · [DLMF §25.4](https://dlmf.nist.gov/25.4) · [mathlib](https://github.com/leanprover-community/mathlib4) · [FLINT](https://flintlib.org/) · [PARI/GP](https://pari.math.u-bordeaux.fr/)

The preprint bibliographies give the wider references for alternating towers and parabolic dynamics. [Reciprocal tetration bibliography](archive/2026-11-18-lean-foundations-v001/papers/foundations/references.bib) · [Dottie spire bibliography](archive/2026-11-18-lean-foundations-v001/papers/dottie-spire/references.bib)
