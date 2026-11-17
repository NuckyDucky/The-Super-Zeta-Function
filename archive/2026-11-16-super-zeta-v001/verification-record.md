# Verification record

16 November 2026. The complete final replay passed **all ten programs in 16.611 seconds**, including process startup, both independent numerical reviews, the evidence audit and offscreen figure generation. Every child returned exit code zero with empty stderr. Exact program hashes and dependency versions are in [replay-results.json](computations/replay-results.json).

Runtime: Python 3.12.11 on Windows 11; mpmath 1.3.0, python-flint 0.9.0, SymPy 1.14.0, NumPy 2.5.5 and Matplotlib 3.11.2. All computations were headless CPU work. Each child had a 60-second timeout. Figures use the `Agg` backend and retained verified numerical records.

## What each program checks

| Program | Precision and actual checks | Scope |
|---|---|---|
| [verify_superzeta_residues.py](computations/verify_superzeta_residues.py) | 25 exact Gamma/binomial residue identities; 16 Acb Mellin integrals at 512 bits; four shifted determinant enclosures; 128 phase roots at 160 decimal digits and 12 positive-integer trace comparisons | Exact symbolic identities; directed integrals plus a proved exponential tail; point spectral sums plus analytic omitted-spectrum bounds |
| [verify_residue_period.py](computations/verify_residue_period.py) | Exact Fraction coefficients, beta moments and ODE recurrence through order 32; exact coverage through 32 chords; four 512-bit AGM certificates including z=1−10⁻⁴⁰; theta checks at 180 digits; three chord-density quadratures at 100 digits | Directed AGM endpoints and independent Acb elliptic integrals; theta and quadrature point evaluations; separately directed density-tail bounds |
| [verify_binomial_normalization.py](computations/verify_binomial_normalization.py) | 384-bit directed arithmetic; 220 exact rational bisections for each of 1,024 quartet levels; exact central binomials; Barnes finite product identities at five cutoffs; controlled radial/Stirling tails; symbolic deformation coefficients through order eight | Directed root, Barnes and full-tail enclosures; exact formal coefficients; independent 100-digit closed constant |
| [verify_signed_histories.py](computations/verify_signed_histories.py) | Exact primitive counts and Euler products; direct finite necklace enumeration; 1024-bit contraction certificate; four distinct phase stages; actual return multiplier/quadratic coefficient/residue/action; independent 220-digit Jacobian and jet derivatives | Computer-assisted existence and local uniqueness in the displayed box; directed negative residue; separate point derivative checks |
| [verify_balanced_charge.py](computations/verify_balanced_charge.py) | 768-bit four-branch invariant-disk certificate; exact lattice/clock counts; all 40 balanced inverse words of lengths two and four; 130-digit quartet/Bessel weights; 1,063 retained joint-product terms | Directed inverse-branch geometry; exact operator identities proved in note; finite point Bessel evaluation plus an exact rational infinite-tail bound |
| [verify_laplace_barnes.py](computations/verify_laplace_barnes.py) | 400-step root bracket with 512-bit signs; 832-bit Barnes coefficient balls; 882 degeneracy and 252 sign checks; 12 independent 90-digit coefficient integrals; 12 directed coupling comparisons; six Laplace asymptotic ratios | Directed coefficient sums plus explicit analytic remainders containing complete frozen reference balls; independent point quadratures and asymptotic illustrations |
| [review_root_coefficients.py](computations/review_root_coefficients.py) | 13 Gamma residues; 16 independent Barnes coefficient integrals at 90 digits; two complex-order Bessel-tail checks | Independent point checks supporting the analytic proof review |
| [review_numerical_scopes.py](computations/review_numerical_scopes.py) | Exact kernel simplification; three independent 90-digit integrals in another endpoint variable; four exact 97-term series intervals enclosing manual AGM balls; fresh 768-bit reconstruction of 12 coupling containments | Independent implementation and numerical-scope review, with frozen-reference hash verification |
| [make_figures.py](computations/make_figures.py) | Two PNG/SVG figures drawn from the verified normalization and signed-fold JSON records | Scientific illustrations of the retained data; internal visual inspection |
| audit_package_evidence.py (original delivery) | Six primary result records; primary-source hashes and byte counts; authored Markdown links and control characters | Evidence/provenance inspection; each required pass condition is asserted |

## Selected explicit certificates

The Barnes–Dottie constant has the directed closed-form enclosure

\[
C_*=[1.22500170731420168529991088115942674601298793731380510396147109231417807414651873
\ \pm2.41\times10^{-81}].
\]

The independently corrected 1,024-level estimator gives

\[
C_*\in[1.22500170731420\pm3.10\times10^{-15}].
\]

At that cutoff, the proved radial log-tail error is below \(1.148215\times10^{-15}\); the Stirling log-tail error is below \(3.464435\times10^{-28}\). These are truncation bounds, in addition to outward rounding.

The ++−− parabolic root is certified inside a real three-dimensional box of radius \(10^{-140}\) around the retained exact decimal-rational center. The strict contraction inequality uses

\[
\|I-A Df(X)\|_\infty<2.79\times10^{-138},\qquad
\|Af(c)\|_\infty<4.15\times10^{-181}.
\]

Its directed iterative residue has real radius below \(1.94\times10^{-102}\); the antiholomorphic half-return proves its imaginary part vanishes exactly. The certificate proves local uniqueness in this retained box.

For the period at \(z=1-10^{-40}\), the manual exact-complement AGM bracket has width below \(1.409\times10^{-151}\). Direct evaluation from a rounded parameter ball has a wider input-conditioned enclosure; the JSON retains both calculations and explains the distinction.

For the Laplace/Barnes coupling series with \(M=36\), the largest error bound among the tested \(s=-1/4,1/4,3/4\) is below \(4.250\times10^{-15}\) at \(\varepsilon=1\) and below \(1.418\times10^{-37}\) at \(\varepsilon=2\). Each directed finite sum plus its analytic tail contains the entire corresponding frozen 512-bit Mellin reference interval.

The charge-projected joint product at the displayed small argument has a proved relative **omitted-product** bound below \(1.198206\times10^{-33}\). Its retained finite sum uses 130-digit point arithmetic. These two numerical scopes are separately recorded.

## Independent review and corrections incorporated

The independent reviews in `review/` check the shifted pole signs and multiplicities, Barnes product constant, all-order continuation formulas, elliptic parameter convention, chord measure, actual signed return order, inverse-branch geometry, prime-clock time and analytic tails. The main review requested explicit normalized branch weights, an expanded Barnes asymptotic showing its constant, and the term “pole index.” Those clarifications are incorporated in the final main report.

An initial shifted-integral implementation encountered nonfinite complex square-root callback intervals. The final computation uses \(u=\sqrt{w+t}\) directly, followed by a fourth-power endpoint substitution, and retains the corresponding proved tail bound at \(u=120\). The complete replay uses this corrected implementation.

## Preservation and package checks

All new research and computation files are in this continuation’s directory. The prior packages supply frozen mathematical inputs with original paths and SHA256 records. The user’s earlier application, cache and rendering workflow were outside this mathematical computation. The final package manifest and ZIP verification record provide file hashes, sizes, syntax/link checks and archive member verification.
