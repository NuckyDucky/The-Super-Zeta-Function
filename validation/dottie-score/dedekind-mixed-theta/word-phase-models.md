# Repeat the marked word and test the boundary

Take the same fixed cap and run its full marked lap twice. The derivative squares. If the first angle is $\pi/6$ or $-\pi/6$, the second is $\pi/3$ or $-\pi/3$. The original symmetric Hurwitz shifts are $1/3,2/3$. The doubled lap selects $1/6,5/6$.

At the same ordinary input $w$, with $w\ne1$, the selected references satisfy

$$
R_1(w)=\pi^{-w}(3^w-1)\zeta(w),\qquad R_2(w)=(2^w-1)R_1(w).
$$

If $0<\Re w<1$, both references have the same zeros and orders as ordinary zeta. The extra factor is holomorphic, changes the contour phase, and has norm at most $3$ when $\Re w\le1$. This transports the original disk estimate for $R_1$ to a three-times larger allowance for $R_2$. The two-lap proof selects the reference from the return angle. Its explicit inputs are the fixed cap and its one-lap angle. [Lean two-lap reference](../../alpoge-super-zeta/DottieTwoLapReference.lean) · [Lean audit](../../alpoge-super-zeta/dottie-two-lap-reference-audit.txt) · [Archived sixths identity](../../../archive/2026-11-19-zero-transport-v001/Dottie-Off-Axis-Return/FlankReferences.lean#L90)

The two signs in each pair select the same corrected reference. The four-stage words “++−−”, “−−++” and the alternating words are distinct entire maps at a nonzero lift. At the resonant cap $L=\pi i$ the six balanced four-stage words share an endpoint and a first derivative, and the second derivative distinguishes their order. The archived flank also has a singular trace normalization at one probe, handled by its continuous reciprocal. [Ordered words](../../../docs/proofs/chronological-order.md) · [Cap derivative index](../../../lean/SuperZeta/CapRecovery/Dominance.lean#L152) · [Archived probe equations](../../../archive/2026-11-19-zero-transport-v001/Dottie-Off-Axis-Return/NOTES.txt)

## Compare both laps on one circle

Use $c=3/4+100000001i$ and $r=31/128$. Take the 96-sample zeta reconstruction with its $10^{-9}$ allowance. Select one constant rotation for each reading from a preliminary phase scan, then enclose the entire circumference by directed intervals.

- The one-lap rotation gives $5|\Re V_1|<9(-\Im V_1)$ on the circle. Two unrotated one-lap readings, at $0/96$ and $45/96$ turns, have angle separation greater than $\arccos(-2/5)$, about $113.58^\circ$.
- The two-lap rotation gives $3|\Re V_2|<4(-\Im V_2)$ everywhere on the circle. This is a cone of width $2\arctan(4/3)$, about $106.26^\circ$.

The first pair of readings separate the one-lap width from the verified two-lap width. The sign for each lap comes from one fixed rotation over its entire circumference. [Circle checker](check-word-phase.py) · [Interval replay](word-phase-interval-audit.txt)

## Supply a field reference without assuming a field zero test

For a field $K$, use the existing completed mixed-theta reading for $F_K$. Its norm on an outer circle is bounded by the absolute theta mass plus the pole term. If samples give a polynomial $S$ with error $E$, take a holomorphic $P$ with $P(z)\ne0$ throughout the disk. If

$$
|S(z)-P(z)|+E\le q|P(z)|\qquad (q<1)
$$

everywhere on the boundary, Lean gives $F_K\ne0$ on the disk and transfers the result to the field's Dedekind continuation. The arc test uses the same $P$ throughout. Multiplying by $-i/P$ places the reading in the lower half-plane with margin at least $1-q$. [Lean field certificate](DedekindMixedThetaSampleModel.lean) · [Printed inputs and axioms](mixed-theta-sample-model-audit.txt)

The Wilson-loop proofs gave a way to choose $P=a e^{b(z-c)}$. If $a\ne0$, the model is entire and never vanishes. Measuring the center value and slope of $G=F/P-1$ gives errors $e_0,e_1$. If $|G|\le M$ in the outer disk of radius $R$, the Schwarz estimate gives

$$
|G(z)|\le e_0+d e_1+(M+e_0+R e_1)(d/R)^2,\qquad d=|z-c|<R .
$$

If the center match is exact, only the quadratic term remains. The replay of the actual ordinary Cayley disk gives an outer bound below $1.01631$ at $R=1/4$, a Schwarz bound below $0.954$ on the inner disk, and a direct interval bound below $0.896$. Separately, the Cauchy derivative budget verifies polygon winding $0$ using 256 vertices for ordinary zeta and 512 for the reading weighted by $(2^w-1)/(2^c-1)$. [Lean exponential model and Schwarz estimate](ContourExponentialModel.lean) · [Lean audit](contour-exponential-model-audit.txt) · [Interval checker](check-exponential-model.py) · [Interval replay](exponential-model-interval-audit.txt) · [Wilson-loop Schwarz and Cauchy source](https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/da7128a36a9c2b3b079c0712f20bae6e126c7dbb/LEAN/CoreLean/CoreLean/SchwarzCauchy.lean#L36-L51)

Two other estimates can carry numerical errors between repeated readings. Close unit return marks satisfy $|a^m-b^m|\le m|a-b|$. If a field or word ratio is proved to equal $\prod_j r_j$ and $|r_j-1|\le\epsilon_j$ throughout the disk, then $|\prod_j r_j-1|\le\exp(\sum_j\epsilon_j)-1$. A sum below $\log 2$ then supplies a uniform relative error below one. [Power perturbation](https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/da7128a36a9c2b3b079c0712f20bae6e126c7dbb/LEAN/CoreLean/CoreLean/ProductExp.lean#L49-L77) · [Product perturbation](https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/da7128a36a9c2b3b079c0712f20bae6e126c7dbb/LEAN/CoreLean/BakerCampbellHausdorff/Product.lean#L62-L68) · [Exponential product bound](https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/da7128a36a9c2b3b079c0712f20bae6e126c7dbb/LEAN/CoreLean/CoreLean/LinkProduct.lean#L53-L58)

## Move the ordinary circle in height

Take the same center $c=3/4+100000001i$, radius $31/128$, and exponential reference $P$. Choose $1/4096$ as the maximum shift along the imaginary axis. The Dottie reference height is the circle's center height plus $1/512$.

If the relative error is at most $0.8954$ on the original circle, then the imaginary part of $-i\zeta/P$ is at most $-0.1046$ there. The outer circle of radius $1/4$ gives a norm bound of $2.01631$ for that weighted reading. With clearance $31/4096$, Cauchy's estimate bounds the change under any of the chosen shifts by $2.01631/31$. So every translated circle keeps a signed margin above $0.039$. The 144-bit and 192-bit interval replays give a lower bound above $0.0396$. [Lean height-band proof](DottieHeightBand.lean) · [Lean audit](dottie-height-band-margin-audit.txt) · [Interval replay](exponential-model-interval-audit.txt)

## Replay

Build the project Lean library on 4.19.0 for the two-lap reference. Compile the archived [FlankReferences module](../../../archive/2026-11-19-zero-transport-v001/Dottie-Off-Axis-Return/FlankReferences.lean) into the same library search path, then check [DottieTwoLapReference](../../alpoge-super-zeta/DottieTwoLapReference.lean). The field and exponential models build with the pinned 4.35.0-rc3 [Alpöge-Dottie replay](replay-alpoge-dottie.ps1) after the sampled contour replay.

From this directory run both interval checks with assertions enabled and python-flint 0.9.0.

~~~text
uv run --with python-flint==0.9.0 check-word-phase.py
uv run --with python-flint==0.9.0 check-exponential-model.py
~~~
