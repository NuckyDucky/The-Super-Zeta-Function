# The Super Zeta Function

NuckyDucky’s reciprocal iteration
$$(P,Q)\longmapsto(e^{LQ},e^{-LP})$$
leads to a spectral zeta function built from the roots of a cosine determinant. A finite orbit of the iteration also gives an explicit height at which to count zeros of the Riemann zeta function. At that height and at twice and three times that height, **every nontrivial zero in the certified intervals is simple and lies on the critical line**.

[Original papers and computations](archive/2026-11-18-lean-foundations-v001/README.md) · [Lean proofs and build instructions](lean/README.md) · [Tagged quartet release](https://github.com/NuckyDucky/The-Super-Zeta-Function/releases/tag/lean-quartets-v1)

## A local strengthening of the seven-eighths theorem

Write $w=\beta+it$ for the Riemann variable. OpenAI’s *Quasi-Riemann Hypothesis*, Theorem 1.1, proves that the half-plane $\beta>7/8$ is zero-free. The Riemann zeta function has a pole at $w=1$. The functional equation and conjugation give the reflected bound, so every nontrivial zero satisfies $1/8\le\beta\le7/8$. **In the three intervals below, the certified counts reduce that entire range to $\beta=1/2$.** In particular they exclude zeros in $1/2<\beta\le7/8$ and in the reflected interval $1/8\le\beta<1/2$, including the endpoints $7/8$ and $1/8$. The strengthening concerns Riemann zeta at the listed heights. [OpenAI, Theorem 1.1](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) · [Functional equation](https://dlmf.nist.gov/25.4)

| Interval in Riemann height $t$ | Simple zeros on $\beta=1/2$ | Off-critical-line zeros |
| --- | ---: | ---: |
| [$\lvert t-T_D\rvert<1/4$](archive/2026-11-17-dottie-local-strip-v001/README.md) | 2 | 0 |
| [$\lvert t-2T_D\rvert\le1/2$](archive/2026-11-18-superzeta-distance-v001/README.md) | 5 | 0 |
| [$\lvert t-3T_D\rvert\le1/2$](archive/2026-11-18-superzeta-distance-v001/README.md) | 4 | 0 |

The argument principle counts zeros with multiplicity from the change in argument around a rectangle. Interval arithmetic certifies the count and rules out zeros on the contour. Each disjoint interval where Hardy’s $Z$-function changes sign gives a distinct zero on the critical line. In each rectangle these sign changes account for the entire count, which proves that every zero is on the line and has multiplicity one.

- At $T_D$, the contour covers $1/16<\beta<15/16$. The entire interval $[1/8,7/8]$ allowed by the seven-eighths theorem and reflection lies inside this contour. [First-height proof and reproduction instructions](archive/2026-11-17-dottie-local-strip-v001/README.md)
- At $2T_D$ and $3T_D$, the computation covers the full closed rectangles $0\le\beta\le1$ and certifies their boundaries to be zero-free. A separate check compares counts from FLINT’s global zero-counting algorithm with the sign changes in the same intervals. [Full-width counts and independent check](archive/2026-11-18-superzeta-distance-v001/README.md)

## How the iteration gives the height

The experiment uses two reflected parameters $L_\pm=\pm x+iy$ with period $320$ under the two-step return, and their midpoint $L_0=iy$. It compares the products of the $320$ logarithmic derivatives at corresponding stages, where a stage $z\mapsto e^{\pm Lz}$ has logarithmic derivative $\pm L$. The modulus ratio is $(|L_\pm|/|L_0|)^{320}$. Taking its logarithm as the scale, the first positive phase change of $2\pi$ fixes the height

$$
T_D=\frac{2\pi}{160\log(1+(x/y)^2)}
=4{,}526{,}119{,}322{,}477.945393\ldots,
$$

with the exact decimal inputs $x=4.749479070945369\times10^{-8}$ and $y=0.509892982511772$. This rule fixed the height before the zeta calculation. In a comparison interval of the same width around the nearest multiple of $\pi$, the count was three, all on the critical line. [Height rule, comparison and certificates](archive/2026-11-17-dottie-grid-match-v001/README.md)

## The spectral zeta and the critical line

Inversion and conjugation of a characteristic phase give four related phases, a *quartet*. In the variable $u$ they give roots $u_n,-u_n,\bar u_n,-\bar u_n$ of $D(u)=\cos^2u-u^2$. The real roots are $\pm d$, where the Dottie number $d>0$ satisfies $d=\cos d$. Squaring the roots gives the spectral values $\lambda_j$, one for each pair related by sign. At coupling $\varepsilon=1$, the spectral zeta is initially $\mathcal Z(s;1)=\sum_j\lambda_j^{-s}$ for $\Re s>1/2$. The paper continues the series meromorphically as the sum of a reference series and an entire Mellin integral correction $J$. Subtracting the correction gives

$$
F(s)=\mathcal Z(s;1)-J(s;1)=2\pi^{-2s}(2^{2s}-1)\zeta(2s).
$$

For $w=2s$ in the open critical strip, the factor multiplying $\zeta(w)$ is nonzero, so the zeros and their multiplicities carry over under this change of variable. The critical line $\Re w=1/2$ becomes $\Re s=1/4$. The seven-eighths bound and reflection give $1/16\le\Re s\le7/16$ for the reconstructed nontrivial zeros, while the three certified intervals put those zeros on $\Re s=1/4$. Their height intervals in $s$ are half as large. [Spectral derivation, equations (21)–(22)](archive/2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md)

Lean proves the complete root list for the cosine determinant, including simplicity and the multiplicity after squaring. The Lean reconstruction uses genus-zero Hadamard factorization as an explicit hypothesis. The zero counts above are proved separately by interval arithmetic. [Quartet proof and factorization step](archive/2026-11-18-quartet-levels-v001/README.md)

## Further results

- **Distance to a zero.** In the rectangles at $2T_D$ and $3T_D$, subdivide the rectangle so that each subrectangle contains one simple zero $s_i$. The minimum-modulus principle gives $|F(s)|\ge\kappa |s-s_i|$, with uniform constants $\kappa=925/256$ and $2407/512$, respectively. A certified upper bound on $|F(s)|$ then gives an upper bound on the distance to that zero. [Bounds and finite Mellin sums](archive/2026-11-18-superzeta-distance-v001/README.md)
- **Motion under truncation.** In two tests, one Newton step predicted the direction in which a zero moved when a term was added to a truncated Mellin sum, with error below $0.001^\circ$. Both tests used known Riemann ordinates as initial guesses. [Newton calculation and interval enclosures](archive/2026-11-17-quartet-angle-v001/README.md)
- **Arithmetic.** The Lean library proves the number of factors of two in every positive-index rational coefficient of the logarithmic derivative and proves that four rational inputs suffice to give the original meme quartic a point over $\mathbb Q_p$ for every prime $p$. [Arithmetic proofs](archive/2026-11-18-binary-law-v001/README.md)

## The factorial correction

Let $R_n$ be the common modulus of the four parameters $L$ obtained from the $n$th quartet of characteristic phases, and set $B_n=4^{-n}\binom{2n}{n}$. The first Stirling correction gives the quarter power in

$$
\lim_{N\to\infty}N^{1/4}\prod_{n=1}^N\frac{R_n B_n^2}{2}
=\frac{e^{\sin(d)/2}}{G(3/2)^2}
=1.22500170731420\ldots,
$$

where $G$ is the Barnes $G$-function. [Derivation and bounds on the omitted terms](archive/2026-11-16-super-zeta-v001/research/binomial-normalization.md)

![Quartet products at five cutoffs from 16 to 1,024 approaching the Barnes–Dottie limit](archive/2026-11-16-super-zeta-v001/figures/barnes-dottie-normalization.png)

## Read and reproduce the work

- [Foundations](archive/2026-11-16-super-zeta-v001/README.md) collects the spectral zeta functions, the order of the exponential compositions, elliptic periods and Barnes normalization.
- [The ordered return](archive/2026-11-17-quartet-return-recursion-v001/README.md) derives the recursion from the two exponential stages and reconstructs a zero near height $32.935$.
- [Tests for off-critical-line zeros](archive/2026-11-17-offcenter-superzeta-v001/README.md) and [the computation at 32 selected heights](archive/2026-11-17-offcenter-screen32-v001/README.md) compare a reflected pair at the same height with two critical-line zeros at different heights.

The dated archives contain the proofs, exact inputs, numerical certificates and instructions for reproducing the calculations. From the repository root, check the archive inventory and SHA-256 hashes with Python 3.

~~~sh
python tools/verify_archive.py
~~~

Cite the relevant proof or certificate by its milestone tag or full commit hash. [Preservation and recovery instructions](PRESERVATION.md)
