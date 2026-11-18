# The exact Stirling correction for the quartet radii

18 November 2026. NuckyDucky identified the cancellation of the leading factorial factors in the original central-binomial normalization. This deposit formalizes the resulting logarithmic correction and its first contribution to the deformed zeta function. It also checks how the correction changes the phase between adjacent levels. [Original normalization, §§1–3](../2026-11-16-super-zeta-v001/research/binomial-normalization.md) · [Original phase calculation](../2026-11-17-quartet-angle-v001/README.md#factorial-phase-between-neighboring-quartet-levels)

## The exact correction

For the characteristic radius $R_n$, set

$$
B_n=4^{-n}\binom{2n}{n},\qquad
D_n=\pi n B_n^2,\qquad
C_n=\frac{R_nB_n^2}{2}=\frac{R_n}{2\pi n}D_n.
$$

Write $\rho_n$ for the logarithm of $n!$ divided by its leading Stirling approximation $\sqrt{2\pi n}(n/e)^n$. Substituting the factorials of $B_n$ gives the exact sum

$$
\log C_n=\log\!\frac{R_n}{2\pi n}+2\rho_{2n}-4\rho_n
=\log\!\frac{R_n}{2\pi n}-\int_0^\infty e^{-nt}\frac{\tanh(t/4)}{t}\,dt.
$$

For real $x>0$ the same negative integral, with $x$ in the exponential, gives $\log[x\,\Gamma(x+1/2)^2/\Gamma(x+1)^2]$. The proof evaluates the change under a unit shift using the Gamma recurrence and Frullani’s integral. Both sides tend to zero as $x\to\infty$ along these shifts, which determines the additive constant. [Exact identities in Lean](../../lean/SuperZeta/StirlingCorrection.lean)

The same cosine reference spectrum that gives the factor multiplying $\zeta(2s)$ also supplies the partial fractions for the kernel:

$$
\frac{\tanh(t/4)}{t}
=8\sum_{j\ge0} \frac{1}{t^2+16\pi^2(j+\tfrac12)^2},
\qquad t>0.
$$

Expanding each denominator by a finite geometric sum gives a signed remainder bounded by the first omitted term. Lean checks that argument at every order, including the summation of the bounds above any positive cutoff. The coefficients are expressed as moments of the reference spectrum and evaluated through even zeta values. At the first order the explicit bound is

$$
0\le \log D_n+\frac{1}{4n}\le\frac{1}{96n^3},\qquad n\ge1.
$$

This turns the original factorial error into a quantity with a known sign and a known maximum at each level. [All-order remainder and cutoff bound in Lean](../../lean/SuperZeta/StirlingExpansion.lean)

## The correction in the zeta series

The characteristic level equation gives the eventual bound $|\log(R_n/(2\pi n))|\le 3n^{-3/2}$. The factorial estimate gives

$$
\left|\log C_n+\frac{1}{4n}\right|\le 4n^{-3/2}
$$

eventually. This is enough to carry the first correction across the domain of convergence of the original Dirichlet series. For a fixed complex parameter $\nu$, write

$$
\begin{aligned}
\mathfrak Z(s,\nu)&=\sum_{n\ge1}n^{-s}C_n^\nu, \qquad \Re s>1,\\
H(s,\nu)&=\sum_{n\ge1} n^{-s}\left(C_n^\nu-1+\frac{\nu}{4n}\right),\\
\mathfrak Z(s,\nu)&=\zeta(s)-\frac{\nu}{4}\zeta(s+1)+H(s,\nu).
\end{aligned}
$$

The power $C_n^\nu$ uses the real logarithm of the positive $C_n$. The remainder $H$ is holomorphic for $\Re s>-1/4$ with $\nu$ fixed or with $\nu$ an entire function of $s$. The coefficient of the pole at zero is exactly $-\nu/4$. Along the spectral diagonal $\nu=-s$, the shifted zeta term tends to $1/4$, the remainder tends to zero, and $\zeta(0)=-1/2$. Thus the continued zeta of the levels $\Lambda_n=nC_n$ has value $-1/4$ at zero. [Radial bound in Lean](../../lean/SuperZeta/QuartetRate.lean) · [Series identity, residue and diagonal in Lean](../../lean/SuperZeta/DeformedZeta.lean)

The continuation to deeper half-planes and the regularized determinant involving the Barnes $G$-function are developed in the written proof. The finite Barnes–Gamma product and the quarter limit also have Lean proofs. [Written derivation](../2026-11-16-super-zeta-v001/research/binomial-deformed-zeta.md) · [Finite product in Lean](../../lean/SuperZeta/Barnes.lean)

## Effect on phase at the Dottie height

The exact neighboring factorial ratio is $D_{n+1}/D_n=1+1/(4n(n+1))$. For $w=\beta+iT$, the factor $C_n^{-w/2}$ contributes the signed phase increment $-\tfrac{T}{2}\log(C_{n+1}/C_n)$ modulo $2\pi$. The table compares its magnitude with a half-turn at the frozen one-winding Dottie height $T_D$. [Exact height inputs](../2026-11-17-dottie-grid-match-v001/dottie-grid-nomination.json)

| Factor in the phase | Above $\pi$ at level | Below $\pi$ at the next level | Verification |
| --- | ---: | ---: | --- |
| $D_n$ | 424,367 | 424,368 | Exact Lean proof using the witness decimals |
| $C_n$ | 424,329 | 424,330 | 384-bit interval bounds for the radii and Lean proof of the comparison |

The full phase uses the logarithmic radial increment in addition to the factorial increment. [The phase proof in Lean](../../lean/SuperZeta/FactorialPhase.lean) checks the full comparison given two rational inequalities. [The directed certificate](phase-bounds.json) supplies those inequalities by isolating each positive characteristic root between rational endpoints. The [uniqueness proof in Lean](../../lean/SuperZeta/QuartetLevels.lean) identifies one positive root at each level. The intervals bracket an adjacent-level phase comparison at the archived height.

## Reproduce the checks

Run from the repository root. The Lean and mathlib versions are pinned by the repository. The numerical replay was run with Python 3.12.11, python-flint 0.9.0, SymPy 1.14.0 and mpmath 1.3.0. The script reads the original witness decimals and root-isolation routine, performs 220 bisections per root, and prints the bounds to standard output.

~~~sh
python tools/check_lean.py --fetch-cache
python tools/verify_archive.py
python -m pip install python-flint==0.9.0 sympy==1.14.0 mpmath==1.3.0
python -B archive/2026-11-18-stirling-correction-v001/verify_phase_bounds.py
~~~

The [archived numerical record](phase-bounds.json) gives the exact endpoints and the directed phase enclosures. The source and output hashes are in the snapshot manifest.
