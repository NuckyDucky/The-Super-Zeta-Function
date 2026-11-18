# The Super Zeta Function

How much can a pair of exponentials tell us about the location of a zeta zero? This repository follows NuckyDucky's reciprocal iteration $(P,Q)\mapsto(e^{LQ},e^{-LP})$ from its four related phase solutions to a spectral zeta function. It contains the derivations, predictions frozen before evaluation, and code for counting the zeros in each tested region.

**[Read the original papers and replay the experiments](archive/2026-11-18-lean-foundations-v001/README.md)** · **[Browse and run the Lean proofs](lean/README.md)**

The Lean library starts with the ordered exponential lift, proves the Dottie fold has negative curvature, reconstructs the fixed pair from its cosine phase, and derives the first four rational determinant traces. Its theorem index gives the hypotheses and evidence for each result.

## From the Dottie number to the critical line

The Dottie number $d$ solves $d=\cos d$. The same cosine equation appears in the spectral construction. At coupling one, subtracting the correction $J$ from the spectral zeta gives the exact identity

$$
\mathcal Z(s;1)-J(s;1)=2\pi^{-2s}(2^{2s}-1)\zeta(2s).
$$

Write $w=2s$. In the open Riemann strip $0<\Re w<1$, the factor multiplying $\zeta(w)$ is nonzero. The reconstructed function therefore has the same zeros and multiplicities in the rescaled coordinates. The Riemann critical line $\Re w=1/2$ appears at $\Re s=1/4$. The experiments ask whether the original dynamics can tell us **where to look** before evaluating zeta there. [Spectral derivation, equation (21)](archive/2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md)

## What the experiments found

| Experiment | Result |
| --- | --- |
| [First Dottie height and matched grid](archive/2026-11-17-dottie-grid-match-v001/README.md) | A finite orbit selected a window centered at $T_D=4{,}526{,}119{,}322{,}477.945393\ldots$. In a window of total height $1/2$, the Dottie arm counted two zeros and the matched grid arm counted three. All were on the critical line. |
| [Full-strip proof at the first height](archive/2026-11-17-dottie-local-strip-v001/README.md) | The directed contour count, two critical-line brackets, and the global $7/8$ bound account for every zero across the critical strip in that Dottie window. Both zeros are simple. |
| [Second harmonic and angular motion](archive/2026-11-17-quartet-angle-v001/README.md) | The window at $2T_D$ contained three simple critical-line zeros. Neither inherited height interval contained a zero. In two separate finite-recursion tests, the next layer predicted a zero's direction of motion to within $0.001$ degrees. |
| [Distance to a zero in two widened windows](archive/2026-11-18-superzeta-distance-v001/README.md) | The full-strip counts at the second and third Dottie harmonics rise to five and four when each window is doubled. All nine zeros are simple and on the line. A lower bound on the magnitude of the reconstructed superzeta turns a small residual into an upper bound on the distance to an individual zero. |

The off-center search remains open at other heights. Each experiment records the function tested, the exact window, and whether a result comes from a finite approximation or a certified count.

## The factorial correction

The same quartet geometry also produces a product with an explicit limit. Let $R_n$ be the radius of the $n$th nonunit quartet and $B_n=4^{-n}\binom{2n}{n}$. Then

$$
\lim_{N\to\infty} N^{1/4}\prod_{n=1}^N \frac{R_n B_n^2}{2}
=\frac{e^{\sin(d)/2}}{G(3/2)^2}
=1.22500170731420\ldots,
$$

where $G$ is the Barnes $G$-function. The quarter power accumulates from the first Stirling correction to the exact factorial ratio. [Derivation and bounds on the omitted terms](archive/2026-11-16-super-zeta-v001/research/binomial-normalization.md)

![Quartet products at five cutoffs from 16 to 1,024 approaching the exact Barnes–Dottie limit](archive/2026-11-16-super-zeta-v001/figures/barnes-dottie-normalization.png)

## Read and reproduce the work

- [Foundations](archive/2026-11-16-super-zeta-v001/README.md) brings together the shifted superzeta, balanced histories, elliptic periods, and Barnes normalization.
- [Ordered quartet returns](archive/2026-11-17-quartet-return-recursion-v001/README.md) derives the recursion from the two exponential stages and reconstructs a zero near height 32.935.
- [Off-center controls](archive/2026-11-17-offcenter-superzeta-v001/README.md) and the [32-level screen](archive/2026-11-17-offcenter-screen32-v001/README.md) document how the search distinguishes a sideways pair from two zeros at different heights.

Each dated snapshot has a README with its proof or experiment, inputs, and replay instructions. To check a clone's file inventory and SHA-256 hashes, run the following from the repository root with Python 3.

~~~sh
python tools/verify_archive.py
~~~

To cite a result, use the snapshot's milestone tag or full commit hash and the path to its proof or certificate. The [preservation guide](PRESERVATION.md) explains how to deposit a correction and restore an archive copy.
