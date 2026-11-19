# Orientation of the period-640 Dottie return from two spectral traces

**NuckyDucky · 19 November 2026**

**Abstract.** Squaring the roots of the marked cosine equation leaves a reflection ambiguity in the angle of a reciprocal exponential return. I resolve it with two labeled reciprocal-root sums. Their difference detects the side of the negative imaginary axis and their joint values recover the unit direction of the return multiplier. On a calibrated interval of the period-640 branch this gives an inverse for the orbit parameter. A directed calculation turns the phase clockwise by 30°, reads the turned orbit, and returns to the original witness within $10^{-29}$ in the parameter. I give the formal argument and the finite interval evidence below.

## From the exponential stages to the spectrum

For $L=iy$ let $F_L(P,Q)=(e^{LQ},e^{-LP})$. Two updates induce $g_L(z)=e^{Le^{-Lz}}$ on the first coordinate. Set $G_y=g_{iy}^{320}$ and let $p_y$ be the limit of iterating $G_y$ from $1$ in the certified cap disk. The corresponding ordered point is $(p_y,\overline{p_y})$. Write $\mu(y)=G_y'(p_y)$ and take $\theta(y)=\arg\mu(y)$ in $(-\pi,\pi]$. Thus the angle measures what **one complete lap** does to a tangent vector. The chain rule gives $\mu$ by multiplying the 640 stage derivatives in that lap. [Cap, multiplier and period in Lean](../../lean/SuperZeta/Oriented/OrderedStages.lean) · [Original finite Dottie witnesses, §8](../2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L554-L604)

I encode a probe angle $a$ by putting $\phi=-a$ and multiplying the outputs of the two stages by opposite unit factors. At a fixed pair of this auxiliary family the actual exponents are $U=LQ$ and $V=-LP$. The following calculation applies to its multiplier-one locus $UV=1$. The native period-640 cycle used to supply $a$ is attracting.

```math
P=e^{-i\phi}e^U,\quad Q=e^{i\phi}e^V,\quad
\alpha=U,\quad V=\alpha^{-1},\quad
\alpha^2 e^{\alpha-\alpha^{-1}}=-e^{2i\phi}.
```

With $2iu=\alpha-\alpha^{-1}$ this gives $u=\sigma\cos(u-\phi)$, $\sigma=\pm1$. Conversely, from such a signed root one recovers $\alpha=\sigma i e^{-i(u-\phi)}$, then $P=e^{-i\phi}e^\alpha$, $Q=e^{i\phi}e^{1/\alpha}$ and $L=\alpha/Q$. Substitution recovers both ordered equations and the unit multiplier. [Marked correspondence in both directions](../../lean/SuperZeta/Oriented/MarkedCharacteristic.lean)

Put $f_{\sigma,\phi}(u)=u-\sigma\cos(u-\phi)$. At $\cos\phi\ne0$ the product below is even in $u$ and gives a normalized entire function in $v=u^2$.

```math
E_{\sigma,\phi}(u^2)
=\frac{f_{\sigma,\phi}(u) f_{\sigma,\phi}(-u)}{\cos^2\phi},
\qquad E_{\sigma,\phi}(0)=1.
```

For each sign, reflection $\phi\mapsto\pi-\phi$ exchanges the two factors up to signs. Consequently the full squared determinant agrees at both reflected phases. In the native angle convention this is reflection across $-90^\circ$ modulo a full turn. Even recording the two unshifted signs in order leaves that ambiguity. [Determinant construction](../../lean/SuperZeta/Oriented/TraceRecovery.lean) · [Exact reflection](../../lean/SuperZeta/Oriented/PhaseSymmetry.lean)

## The two-trace inverse

**Proposition.** For a regular probe let $M(a)$ denote the sum of $1/v$ over the zeros of $E_{+,-a}(v)$. At two regular offsets set $M_\pm=M(\theta\pm\pi/6)$ and $S_\pm=1-2/M_\pm$. Then

```math
M(a)=\frac{2}{1-\sin a},\qquad
e^{i\theta}=(S_+-S_-)+i\,\frac{S_++S_-}{\sqrt3}.
```

**Proof.** The positive-sign determinant has simple zeros and grows at most as $\exp(K(1+\sqrt{|v|}))$ for a phase-dependent $K$. Counting its zeros in disks gives absolute summability of their reciprocals. Its normalized genus-zero product runs over its actual zero set. Differentiation at the origin therefore gives $M(a)=-E_{+,-a}'(0)$. The Taylor coefficient from the signed product gives the displayed expression for $M(a)$. Now $S_\pm=\sin(\theta\pm\pi/6)$, and the difference and sum of these two sines are respectively $\cos\theta$ and $\sqrt3\sin\theta$. [Simplicity and growth](../../lean/SuperZeta/Oriented/TwistedGrowth.lean) · [Counting bound](../../lean/SuperZeta/Oriented/GrowthCount.lean) · [Product](../../lean/SuperZeta/Oriented/GrowthProduct.lean) · [Differentiation](../../lean/SuperZeta/Oriented/ProductTrace.lean) · [Integrated inverse theorem](../../lean/SuperZeta/Oriented/SpectralInverse.lean)

In particular the sign of $M_+-M_-$ is the sign of $\cos\theta$. On $(-120^\circ,-60^\circ)$ it specifies the side of $-90^\circ$. At the pivot the two shifted readings are regular and equal $8-4\sqrt3$. The unshifted normalization is singular there. At the two ends of this sector one of the shifted probes becomes singular.

## Returning to the witness

I used the original centerline midpoint $y_0=0.509892982511772$ and the interval $I=[0.50989298230,0.50989298314]$. The 448-bit calculation encloses the cap in an invariant disk around $1$ of radius $10^{-15}$. The scalar lap contracts there by a factor below $7.49\times10^{-16}$. Disjointness at scalar iterates 64 and 160 excludes every proper divisor of 320. Since 320 is even, the primitive ordered period is 640. On 15 subintervals covering $I$, the implicit derivative of the cap point gives $1.80\times10^{11}<d\theta/dy<1.93\times10^{11}$ in **degrees per unit of $y$**. The principal argument stays continuous throughout. Every target in this angle range therefore has exactly one parameter in $I$. [Branch certificate](data/orbit_crossing.json) · [Branch inverse](../../lean/SuperZeta/Oriented/BranchInverse.lean)

| Step | Centerline parameter $y$, rounded | Native angle | $M_+$ | $M_-$ |
| --- | ---: | ---: | ---: | ---: |
| Read the witness | 0.509892982511772 | −86.2334491153° | 1.092114929871 | 1.054295997754 |
| Move clockwise by 30° and read again | 0.50989298234830295220 | −116.2334491153° | 1.001081173287 | 1.285503688169 |

I solved for the second parameter from the first pair, then evaluated both determinants anew on its enclosed orbit. Applying the inverse to these fresh readings, turning the recovered unit direction back by $+\pi/6$, and inverting the branch gave the original rational $y_0$ in an interval of width below $10^{-29}$. The two-probe calculation obtains each root sum from the determinant coefficient. The proposition proves that this evaluates the complete reciprocal-root sum. A second computation isolates nonreal signed roots directly and encloses the same returned parameter within width $1.44\times10^{-45}$. [Trace round trip](data/quarter_probe.json) · [Signed-root round trip](data/spectral_roundtrip.json)

What returns is a **rooted orbit**. The parameter fixes $L=iy$, the cap picks the same distinguished point on the cycle, and the ordered map fixes its itinerary. At each step the actual exponents recover the inputs as $(P,Q)=(-V/L,U/L)$. As a finite cross-check I compared both exponents at each of the 640 steps. All 1,280 returned enclosures overlapped their original partners. The identification of the orbit follows from uniqueness on $I$. [Ordered lifts and their integer sheets](../../lean/SuperZeta/Oriented/OrderedStages.lean) · [Trace and exponent enclosures](data/quarter_probe.json)

## The arithmetic reference at the two absolute angles

The offsets used to read a witness and the absolute angles where the reference simplifies are distinct quantities. At an **absolute** native angle $a$, the reference determinant is $\cos(u-\phi)\cos(u+\phi)/\cos^2\phi$ with $\phi=-a$. Its first reciprocal-root coefficient is $1/\cos^2\phi$. In the positive-sign spectrum the difference of first coefficients is

```math
\frac{1-2\sin\phi}{\cos^2\phi}.
```

Thus at native $a=-\pi/6$ the coefficients agree at $4/3$ and the first correction is zero. At $a=+\pi/6$ the dynamical coefficient is $4$ and the reference coefficient is $4/3$, leaving $8/3$. The branch calculation brackets native returns of both absolute angles. [First-coefficient identities](../../lean/SuperZeta/Oriented/FirstCorrection.lean) · [Native crossings](data/orbit_crossing.json)

For $b=1/2-a/\pi$ these absolute angles give $b=2/3$ and $1/3$. The reference zeros have the two squared progressions $\pi^2(n+b)^2$ and $\pi^2(n+1-b)^2$, $n\ge0$. Write $w=2s$. Summing those reference spectra for $\Re w>1$ gathers the positive integers in residue classes 1 and 2 modulo 3. Continuing away from $w=1$ gives

```math
\pi^{-w}[\zeta(w,1/3)+\zeta(w,2/3)]
=\pi^{-w}(3^w-1)\zeta(w).
```

For $\Re w>0$ the prefactor is nonzero. Liu's Theorem 1.1 gives the strict zero-free half-plane $\Re w>B_*$, $B_*=0.8733458561067185768\ldots$, for unitary Hecke $L$-functions, allowing the norm-character pole. I specialize Liu's result to the trivial character over $\mathbb Q$. It gives $\Re s>B_*/2=0.4366729280533592884\ldots$ for this reference, away from its pole. Liu obtains the exponent from joint moments of inverse and ordinary character sums in zero detection. Here the two orientations have the same arithmetic reference while their dynamical first corrections differ. The formal transfer takes the zero-free bound as an explicit external hypothesis. [Baiying Liu, *Joint marked moments and optimized zero-free half-planes for unitary Hecke L-functions*, Hexagon 2611.00421v1, 13 November 2026, Theorem 1.1 and §1.2](https://hexagonmath.org/pdf/2611.00421v1#page=2) · [Preprint record](https://hexagonmath.org/2611.00421v1) · [Formal reference identity](../../lean/SuperZeta/Oriented/LiuConnection.lean)

## Verification and reproduction

The deposit adds 12 Lean modules with 88 public theorems. The full project build and axiom audit passed for 1,026 theorem declarations. Its allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. A separate replay, given only the current numerical sources and the original disk verifier, regenerated all three JSON records byte for byte in the recorded environment.

| Evidence | Scope |
| --- | --- |
| Lean 4.19.0 | The actual lifted stages and multiplier, the marked characteristic in both directions, reflection, convergence and product on the full positive-sign zero set, and the two-trace inverse. The parameter inverse requires a continuous angle of positive derivative on the chosen interval, regular probes at the readouts and the turned target in range. Lean also checks the rational endpoints of the two-trace return. |
| Directed interval arithmetic | Cap capture from the given starting point, primitive period, enclosure of the derivative on the designated branch, the fresh measurements and return enclosures. Decimal entries in the table are rounded for reading. Exact inputs and output bounds are in the JSON records. |
| External arithmetic theorem | Liu supplies the exponent in the zero-free transfer for the third-residue reference. The orbit inverse is proved independently of that arithmetic input. |

From the repository root, use Python 3.12 with python-flint 0.9.0 and mpmath 1.3.0. The commands use the original disk arithmetic from the prior snapshot and emit fresh records. They use deterministic rational inputs and a precision of 448 bits. The proof build uses the pinned Lean and mathlib versions.

~~~sh
python tools/check_lean.py --fetch-cache
python -B archive/2026-11-19-oriented-return-v001/computations/orbit_crossing.py
python -B archive/2026-11-19-oriented-return-v001/computations/quarter_probe.py
python -B archive/2026-11-19-oriented-return-v001/computations/spectral_roundtrip.py
python tools/verify_archive.py
~~~

I developed this extension against research revision [98aff0b](https://github.com/NuckyDucky/The-Super-Zeta-Function/tree/98aff0b98ef8267332b84912a465750b1396765f). This is the first deposit of the oriented return. The Lean sources are integrated in [SuperZeta/Oriented](../../lean/SuperZeta/Oriented), the [original finite-orbit verifier](../2026-11-17-quartet-return-recursion-v001/computations/verify_dottie_horn_slice.py) supplies the disk propagation, and the [figure source](figures/plot_oriented_traces.py) reads the measured traces from this deposit. [Source inventory and provenance](provenance.json) · [Return to the main paper](../../README.md#oriented-period-640-return)
