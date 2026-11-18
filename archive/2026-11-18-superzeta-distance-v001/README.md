# How small can the reconstructed superzeta be away from a zero?

We give an explicit lower bound on the magnitude of the reconstructed superzeta throughout two rectangles, and a way to turn a measured residual into a certified position error. The rectangles use two previously selected heights from the finite Dottie witnesses. Each extends half a Riemann height unit above and below its center, twice the vertical coverage of the earlier half-unit windows.

| Riemann window center | Counts in successive quarter-height slices, bottom to top | Simple critical-line zeros | Off-line zeros | Lower bound coefficient in superzeta units |
|---|---|---:|---:|---:|
| $2T_D$ | 0, 2, 1, 2 | 5 | 0 | $925/256$ |
| $3T_D$ | 2, 0, 2, 0 | 4 | 0 | $2407/512$ |

The last column is a certified constant $\kappa$ such that $|F(s)|\ge\kappa |s-s_i|$ throughout the horizontal cell assigned to zero $s_i$. At the pair of trial real parts $1/8$ and $3/8$, this gives $|F(s)|\ge925/2048$ in the first window and $|F(s)|\ge2407/4096$ in the second, uniformly in height. [Second harmonic bounds](distance-h2.json) · [Third harmonic bounds](distance-h3.json) · [Independent review](REVIEW.md)

**Seven regrouped blocks of the project's Mellin recursion meet this test.** In each window a specified finite analytic function has exactly one zero near each full root and none elsewhere. The finite-to-limiting root distances in superzeta coordinates are below $0.0000216$ and $0.0000252$, respectively. With 21 blocks the distances fall below $6.0\times10^{-59}$ and $7.1\times10^{-59}$. Each block sums a specified combination of the original layers. [Finite reconstruction and uniform tail proof](NATIVE.md)

## Coordinates and domain

Let $w=2s=\beta+iT$ and use the exact identity of the [reciprocal cosine spectrum, equations (21)–(22)](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md):

$$
F(s)=\mathcal Z(s;\varepsilon)-J(s;\varepsilon)
=2\pi^{-2s}(2^{2s}-1)\zeta(2s),\qquad \varepsilon>0 .
$$

The residual is the magnitude of this complex difference. It is the same for every positive coupling. The two heights $H=kT_D$, for $k=2,3$, use the [archived finite-orbit clock](../2026-11-17-dottie-grid-match-v001/dottie-grid-nomination.json):

$$
T_D=\frac{2\pi}{160\log(1+(x/y)^2)},\qquad
x=4.749479070945369\times 10^{-8},\qquad y=0.509892982511772 .
$$

Treat these terminating decimals as exact inputs. We work in the **closed** rectangles $0\le\beta\le1$, $|T-H|\le1/2$. The corresponding superzeta rectangles have $0\le\Re s\le1/2$, $|\Im s-H/2|\le1/4$. The previously used harmonics were selected in earlier work. The wider windows and the count protocol were recorded in [the plan](coverage_plan.json) before the new counts. The bound below is in the normalization of $F$ displayed above.

## Local factorization and position error

Write $G(w)=F(w/2)$. The full-strip winding counts and disjoint critical-line sign brackets certify all of the zeros in each rectangle, with multiplicity. Every one is simple and has the form $\rho_i=1/2+i\gamma_i$. The prefactor of zeta can vanish only when $\beta=0$ and $T\log2\in2\pi\mathbb Z$. The edge calculation below checks its nonvanishing on the full left edge in each window.

Sort the brackets by height. Between successive brackets place a horizontal cut halfway between the upper endpoint of the lower bracket and the lower endpoint of the upper bracket. This partitions each rectangle into closed cells with disjoint interiors, one zero per cell. In cell $i$, define

$$
Q_i(w)=\frac{G(w)}{w-\rho_i},\qquad Q_i(\rho_i)=G'(\rho_i).
$$

This removes the known simple zero. The quotient extends holomorphically and has no zeros on the closed cell. On each boundary segment we enclose the ratio

$$
\frac{2\pi^{-\beta}\,|2^w-1|\,|\zeta(w)|}{|w-\rho_i|}
$$

using an interval for the unknown ordinate $\gamma_i$. A certified boundary lower bound $c_i>0$ extends to the entire cell by the maximum-modulus principle applied to $1/Q_i$. In particular

$$
|F(s)|\ \ge\ 2c_i|s-\rho_i/2|
\ \ge\ 2c_i\left|\Re s-\tfrac14\right|.
$$

The first inequality bounds **both** components of a position error. If a computed approximation gives $\widetilde F(s)=0$ and a rigorous truncation/evaluation error $|F(s)-\widetilde F(s)|\le\eta$, the true zero in that cell is within $\eta/(2c_i)$ of the computed location. More generally, a certified nonzero approximate residual adds $|\widetilde F(s)|$ to the numerator. This estimate requires the address to lie inside the certified cell. It applies at shared cell boundaries using either neighboring bound. At the zero it also yields $|F'(\rho_i/2)|\ge2c_i$.

**When an approximation is guaranteed to find every zero.** In the $s$-plane take a disk of radius $1/1000$ about each true zero. The rational brackets put each closed disk strictly inside its own cell. If an approximation is holomorphic on a neighborhood of the rectangle and its uniform error relative to $F$ is at most $3/1000$ there, then it has exactly one zero in each of these disks and no other zero in the rectangle. On each circle the lower bound for $|F|$ strictly exceeds $3/1000$, so Rouché's theorem preserves the count of one, including multiplicity. At every point outside the disks the same strict lower bound excludes an additional zero. The error hypothesis is a requirement on the particular approximation being used. [Exact disk and threshold checks](check_stability.py)

The [OpenAI quasi-Riemann theorem](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md), combined with zeta reflection, gives $1/16\le\Re s\le7/16$ for every reconstructed nontrivial zero. Our finite-window proof uses directed counts and the minimum-modulus estimate independently of that theorem. The constants refer only to the stated rectangles.

## How the computations certify the statements

- **Coverage.** Four adjacent quarter-height rectangles tile each Riemann window. Interval winding of zeta along each boundary counts every interior zero with multiplicity and proves all boundaries are zero-free. Disjoint opposite signs of the real Hardy function on the critical line locate that many distinct zeros. This accounts for the interiors and the seams. [Contour and bracket verifier](coverage.py)
- **Uniform interpolation error.** Each quarter-height chart samples the analytic zeta function at 192 equally spaced points of radius $r=103/200$. On the outer circle of radius $R=9/10$, the two-term Euler–Maclaurin bound gives $M=(H_{\rm chart}+3)^2$. The Fourier interpolation error on $|w-w_{\rm chart}|\le a=261/500$ is at most $MR(r^{192}+a^{192})/((R-a)(R^{192}-r^{192}))$, by the Cauchy coefficient bound, geometric tail, and aliasing of coefficients whose indices agree modulo 192. Interval evaluations include this error and numerical rounding. [Chart evaluator](coverage_chart.py)
- **Distance.** Interval enclosures cover entire boundary segments. Segments are subdivided until a positive lower bound is certified. Each published cell constant $c_i$ is rounded downward to a multiple of $1/1024$. [Distance verifier](distance.py)

All offsets in the machine-readable records use Riemann height units relative to the exact clock $H$. The contour and distance proofs run at 192 bits. A second argument uses FLINT's rigorous global zero counter at 96 bits and direct interval evaluations at 128 bits of the signs on both ends of every bracket. Both arguments use the same FLINT library. [FLINT's zero-count and isolation algorithm](https://flintlib.org/doc/algorithms/special-functions/zeta-zeros.html)

## Reproduce the contribution

Use Python 3.12 with python-flint 0.9.0. The original run used Python 3.12.11 and FLINT 3.6.0. From this snapshot directory, start with an empty output directory. Keep ordinary Python assertions enabled. The scripts refuse to overwrite result files.

~~~sh
python -m pip install python-flint==0.9.0
mkdir replay
python -B coverage.py 2 replay/coverage-h2.json
python -B coverage.py 3 replay/coverage-h3.json
python -B coverage_check_counts.py replay/coverage-global-counts.json
python -B coverage_check_signs.py replay
python -B coverage_indexed.py replay/coverage-indexed.json
python -B distance.py replay/coverage-h2.json replay/distance-h2.json
python -B distance.py replay/coverage-h3.json replay/distance-h3.json
python -B check_stability.py replay
python -B independent_distance.py replay/coverage-h2.json replay/distance-h2.json
python -B independent_distance.py replay/coverage-h3.json replay/distance-h3.json
python -B native_complete.py
~~~

Compare the integer counts, rational brackets, and rational distance bounds to the deposited JSON records. The repository's archive verifier checks the original file hashes.
