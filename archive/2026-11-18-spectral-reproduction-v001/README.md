# Reproduce the quartet determinant, the Dottie periods and the three zeta counts

I would particularly welcome a reproduction with a different operator discretization or a different rigorous zeta evaluator. I give the inputs and expected results here so a reader can report a disagreement at the level of a particular eigenvalue, contour edge, or sign bracket. The runs recorded here are internal replays. The contour and global-count routes use different algorithms in the same FLINT library.

## Which spectrum does the determinant reproduce?

At unit coupling the squared roots are the Dottie square $d^2$ and two conjugate values $u_n^2,\bar u_n^2$ for each nonreal quartet. Squaring identifies the two signs. Recover the ordered phases using the sign in $u=\sigma\cos u$ before taking the square. As a check on the indexing, counting all four signs again doubles the nonreal contribution to the first trace. The correct full trace is $d^{-2}+2\Re\sum_{n\ge1}u_n^{-2}=2$. [Phase recovery and traces, eqs. (3)–(5), (16)–(19)](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md)

| Object | What an independent reader can check |
| --- | --- |
| Scalar determinant at unit coupling | Every complex $v$ satisfies $E(v)=\prod_j(1-v/\lambda_j)$. Check the full simple-root list, $\sum_j\lvert\lambda_j\rvert^{-1}<\infty$, growth order at most $1/2$, and $E(0)=1$. Together these fix a genus-zero product of ordinary linear factors and its constant. [Concrete Lean theorem](../../lean/SuperZeta/UnitSpectrum.lean) |
| Boundary operator | Solve the eigenfunction and inverse problems with $c=f(0)$ on $L^2(-1,1)\oplus\mathbb C$. For $\varepsilon\ne0$ its inverse $B_\varepsilon$ is Hilbert–Schmidt. Its square is trace class. The manuscript proves $\det(I-v B_\varepsilon^2)=\cos^2\sqrt v-v/\varepsilon^2$ using finite matrices with explicit approximation bounds. This operator identity has a written proof. [Equations (6)–(15)](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md#2-a-boundary-operator-with-compact-inverse-and-the-cosine-spectrum) |
| Precedent | Hupkes gives a derivative with a midpoint condition on a continuous-history space. With equal endpoint weights $i\varepsilon/2$ his characteristic function specializes to $\Delta(iu)=i(u-\varepsilon\cos u)$. The state space, explicit inverse-square determinant, and recovery of both reciprocal phases specify the comparison to make when looking for an earlier construction. [Hupkes, chapter 2](https://math.leidenuniv.nl/scripties/PhdHupkes.pdf) |
| Variants | For $\Re\varepsilon>0$ the principal-cut zeta exists, initially on $\Re s>1/2$. A real shift $a\ge0$ replaces $\lambda_j$ by $\lambda_j+a$. For $a>0$ the shifted poles are $s=1/2-n$ with residues $\binom{2n}{n}a^n/(4^n\pi)$. For a complex shift continue locally off the rays $-\lambda_j-[0,\infty)$. The signed-word construction also gives a separate lattice operator whose return moments count balanced pairs of words. [Shift and residues](../2026-11-16-super-zeta-v001/research/shifted-superzeta.md) · [Lattice operator and moments, eqs. (1)–(6)](../2026-11-16-super-zeta-v001/research/balanced-charge-operators.md) |

The boundary operator has the cosine roots as eigenvalues. The nontrivial Riemann zeros occur where the continued quartet sum equals its relative correction, $\mathcal Z(s;1)=J(s;1)$ in $0<\Re s<1/2$. Constructing an operator whose eigenvalues themselves select those Riemann heights is a further open question for this work. [Reconstruction and orders of zeros in Lean](../../lean/SuperZeta/UnitSpectrum.lean)

## The Mellin integral and its branch

Use $-\pi<\arg\lambda_j<\pi$ for the squared eigenvalues, and the real logarithm of $E(-t)>0$ for $t\ge0$ at unit coupling. In $1/2<\Re s<1$, integrate the full logarithmic derivative on that ray. Divide out $\cosh^2\sqrt t$ and integrate the remaining logarithmic derivative by parts. The relative logarithm is $O(t)$ at zero and $O(t e^{-2\sqrt t})$ at infinity. This gives the uncontinued relative integral on $\Re s<1$. Subtracting successively more Taylor terms at zero and multiplying by $\sin(\pi s)$ gives the entire correction. A change of logarithm for an individual root changes its complex power, so matching the cut is part of reproducing the result. [Derivation, eqs. (20)–(23)](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md#5-a-two-variable-zeta-for-the-inverse-cosine-coupling-family)

At $s=(3+i)/4$ and $\varepsilon=1$ I evaluated the full integral directly and separately added the relative integral to the double half-integer reference. Both give about $1.6529717709207846941-0.3532241045064131662i$. At 192 bits their difference encloses zero, with absolute component bounds of $1.35\times10^{-20}$ (real) and $1.36\times10^{-20}$ (imaginary), including the omitted tails. The analytic proof covers the common strip. The numerical check exercises both formulas at one nonreal argument. [Two integrals and explicit tails](check_complex_mellin.py)

## From a finite Dottie orbit to a limiting horn

The centerline half-step is $H_y(z)=e^{iy\bar z}$, and the return on one phase is $H_y^2$. At 384 bits I tracked the marked cap $1$ into a trapping disk over each **closed parameter interval** below. Each full return maps its disk strictly inside itself, has derivative norm below one, and excludes a return at each maximal proper divisor of its claimed period. [Centerline verifier](check_spire_windows.py) · [Original finite windows and off-axis witnesses](../2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L554-L604)

| Center of $y$ interval, radius $10^{-13}$ | Primitive period under $H_y$ | Primitive period under $H_y^2$ |
| --- | ---: | ---: |
| 0.5098930698771419799831 | 639 | 639 |
| 0.5098929835386691077069 | 640 | 320 |
| 0.5098928862668716592052 | 641 | 641 |

There is also a separate three-point certificate at $y=0.509892982511772$ for the midpoint and two reflected off-axis flanks. It checks both marked scalar returns starting from the cap. The preprint follows the period-640 cycle with its 25/295 itinerary over a finite slab. The open step is to follow the same cap orbit from entry to exit, keep the same lifted logarithm, and enclose the change between the attracting and outgoing phase coordinates all the way to a specified limiting horn. Three separated slabs and the local quotient estimate leave an interval of this transport unaccounted for. The rail law on the $p^{-2}$ scale is conditional on this matching. Whether the reflected witnesses belong to different horn components remains open. [Three-point verifier](../2026-11-18-lean-foundations-v001/checks/dottie_slice.py) · [Conditional rail law](../2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L609-L642) · [Finite bridge and precise gap](../2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L739-L750)

## Which segments and which zeros were counted?

The frozen clock uses the period-320 scalar lap, the flank-to-center modulus ratio, and a chosen one-winding convention. It gives $T_D=4526119322477.945393\ldots$ before evaluating zeta. In the matched experiment, the Dottie interval and the nearest $\pi n$ interval had equal width. They contained two and three simple line zeros respectively, with zero sideways pairs in either. Whether the dynamics improves height selection remains open. A useful independent test would freeze further orbit-selected heights, equal-width grid controls and a comparison statistic before evaluating either arm. [Frozen inputs and matched results](../2026-11-17-dottie-grid-match-v001/README.md)

| Center | Half-width in Riemann height | Windings, lowest slice first | Disjoint Hardy brackets | Off-line zeros |
| --- | ---: | --- | ---: | ---: |
| $T_D$ | $1/4$ | 1, 1 | 2 | 0 |
| $2T_D$ | $1/2$ | 0, 2, 1, 2 | 5 | 0 |
| $3T_D$ | $1/2$ | 2, 0, 2, 0 | 4 | 0 |

- **Contour.** Enclose the image of each entire oriented boundary segment under $\zeta(w)$, including shared edges. An enclosure excludes zero and bounds the change of argument. Summing these changes gives an integer winding for each slice. The first contour used $1/16\le\Re w\le15/16$. Its published full-strip corollary uses the reflected 7/8ths bound. Both higher contours span $0\le\Re w\le1$ directly. [First contour and corollary](../2026-11-17-dottie-local-strip-v001/README.md) · [Higher contours, interpolation remainder and commands](../2026-11-18-superzeta-distance-v001/README.md#how-the-computations-certify-the-statements)
- **Analytic error.** On each chart, enclose the sampled values, bound the analytic tail and aliasing on a larger circle, and add that bound when evaluating the interpolant on each segment. The rechecked uniform interpolation-error bounds were below $1.008\times10^{-15}$, $7.940\times10^{-20}$ and $1.787\times10^{-19}$ at the respective heights. These are bounds on the chart approximation. The segment enclosures also include arithmetic rounding and variation along the segment. At the two higher heights a different 145-node whole-window computation reproduced windings 5 and 4 and all nine cellwise distance bounds for the reconstructed function, including its elementary prefactor at the left edge. [Chart bound](../2026-11-18-superzeta-distance-v001/coverage_chart.py) · [Alternative charts and distance tests](../2026-11-18-superzeta-distance-v001/independent_distance.py)
- **Hardy signs.** The two endpoints of each critical-line bracket have rigorously opposite signs. Its interior therefore contains a zero. All eleven brackets are disjoint within their windows. Their number equals each contour count with multiplicity, so each contains one simple zero and every zero in the three windows is accounted for. [Archived brackets](../2026-11-18-superzeta-distance-v001/README.md) · [First-height record](../2026-11-17-dottie-grid-match-v001/dottie-grid-certificate.json)
- **Independent counting method.** At 96 bits, FLINT’s global count gives one integer on a guard of radius $2^{-18}$ around each of the 13 cut heights. Subtract consecutive integers and recover all ten slice counts in the table. At 128 bits, direct evaluation of Hardy’s function recovers all 22 endpoint signs. This route also checks the full strip at the first height directly. A reproduction using another rigorous arithmetic library would be especially valuable. [Guarded counts and direct signs](check_three_counts.py) · [FLINT’s algorithms](https://flintlib.org/doc/algorithms/special-functions/zeta-zeros.html)

## Run from a fresh checkout

Use Python 3.12 with assertions enabled. The replays used Python 3.12.11, python-flint 0.9.0 (FLINT 3.6.0), SymPy 1.14.0 and mpmath 1.3.0. Run the following commands from the repository root.

~~~sh
python -m pip install -r archive/2026-11-17-offcenter-superzeta-v001/requirements.txt
python -m pip install sympy==1.14.0 mpmath==1.3.0
python -B archive/2026-11-18-spectral-reproduction-v001/check_complex_mellin.py
python -B archive/2026-11-18-spectral-reproduction-v001/check_spire_windows.py
python -B archive/2026-11-18-lean-foundations-v001/checks/dottie_slice.py
python -B archive/2026-11-18-spectral-reproduction-v001/check_three_counts.py
python -B archive/2026-11-17-dottie-local-strip-v001/replay.py
~~~

For the original spectral verifier, copy its source to a fresh scratch directory. It writes the results next to the script. These commands work from the root in a POSIX shell or PowerShell.

~~~sh
mkdir spectral-replay
cp archive/2026-11-18-spectral-reproduction-v001/verify_cosine_spectrum.py spectral-replay/
python -B spectral-replay/verify_cosine_spectrum.py
~~~

Compare its JSON with the [deposited spectral results](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum-results.json), omitting only elapsed time. All mathematical fields matched in the replay. It includes 12 exact trace polynomials, three exact finite matrices, 128 quartet representatives evaluated at 140 decimal digits, 36 directed projection checks and 10 directed relative Mellin integrals at 512 bits. The 128 root values are point calculations. The all-root statement comes from the proof.

Run the [full higher-height contour and distance instructions](../2026-11-18-superzeta-distance-v001/README.md#reproduce-the-contribution) to reconstruct the chart, boundary and distance records. Run the [Lean build](../../lean/README.md) for the unit-coupling determinant, root sum and multiplicities. The three height certificates and the finite trapping windows are directed numerical proofs outside that Lean build.

## Provenance

This 18 November 2026 deposit supplements the original [spectral construction](../2026-11-16-super-zeta-v001/README.md), [Dottie preprint](../2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex), [first-height count](../2026-11-17-dottie-local-strip-v001/README.md) and [higher-height counts](../2026-11-18-superzeta-distance-v001/README.md). The original project source was `computations/verify_cosine_spectrum.py`. Its SHA-256 is `b5d282d30aa5d83222be419b6359056ae52fb4d8129bd7d7c278bca726d92345`. It is reproduced byte for byte. The other three verifiers were written for this deposit.
