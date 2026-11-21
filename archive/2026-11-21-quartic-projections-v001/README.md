# The factorial exponent, the quartic branch and the signed prime windows

I used the error in Stirling’s formula to recover the exponent of a quadratic unit. For the Gaussian quartic I tested two other predictions against its prime signs. One predicts which way a complex reading points. The other predicts which prime-cutoff intervals already contain too much positive area for a particular zero-exclusion test.

| Question | Calculation | Consequence |
|---|---|---|
| Which powers of $6+\sqrt{35}$ can come from $n!+1=m^2$? | The largest prime divisor of $35$ restricts $n$ to $7,\ldots,13$. Only $7!$ has squarefree part $35$. Four balanced binomial readings enclose the exponent. | The only positive solution with squarefree part $35$ is $71+12\sqrt{35}=(6+\sqrt{35})^2$. The squarefree part $70$ admits no solution at any exponent. [Factorial and Pell proof](stirling-pell.md) |
| Can the Gaussian signs distinguish the two conjugate quartics in one complex reading? | Keeping $+i$ fixed, the Fourier transform predicts a line for each branch. Summing the original signs at balanced smoothing independently encloses the complex value. | The measured angle is $-0.401905193375097\pm1.2\times10^{-14}$ radians. Using the eighth angular power doubles the predicted angle. Its direct sum gives $-0.803810386750194$ radians, with absolute error below $7.9\times10^{-12}$. Conjugation reverses each angle. The two lines also apply to nonzero readings of the completed angular function on the critical line. [Derivation and measurement](angular/README.md) |
| Does a passing prime window continue to pass when I double its starting cutoff? | At exponent $1/8$, the weighted positive area passes at $Y=2048$ and exceeds the allowance at $Y=4096$. Every later window must include its own share of the area already measured. | At this exponent all real starts from $4096$ to $19{,}252$ fail. At exponent $1/32$ all real starts from $2048$ to $4{,}762{,}984$ fail. These bounds concern one sufficient test for zeros. [Window calculation and projection](windows/README.md) |

### The same scalar Gaussian factor in two fields

For $\delta=-5045155+1027708i$ and $D=|\delta|^2$, the scalar Gaussian factor of my quartic is also an unramified order-four class-character series over $\mathbb Q(\sqrt{-D})$. At norm $73$, the two Gaussian primes have opposite signs. The other quadratic field has no ideals of norm $73$. Both descriptions give coefficient zero. I checked the correspondence at all ideal norms through $4096$, then used two binary quadratic forms to predict sixteen prime traces before evaluating their Gaussian signs. The [field derivation and class-group computation](fields-and-windows.md) explain which classes require a complex parameter in the original tower. The [Fourier derivation](quartic-dual-theta.md) identifies the frequencies that survive when I sum the signs on the Gaussian lattice.

### Lean and the external window theorem

The three Lean files here use the external project’s mathlib version 4.33.1. The repository’s [factorial reconstruction](../../lean/SuperZeta/StirlingCorrection.lean) has its own toolchain. The new finite Fourier identities, scale identities and residue inequalities were checked from source. The [fixed-squarefree-part classification](../../lean/SuperZeta/FactorialPell.lean) uses the repository’s main Lean project. The propagated index error, field identification, Poisson specialization and directed numerical estimates have the proofs and replays linked above.

The [quartic Lean project](../../lean-ideal73/lakefile.toml) pins the same mathlib revision. From its directory, run `lake env lean` on the absolute path of each of [ScaleAndShape.lean](ScaleAndShape.lean), [DyadicPoleFilter.lean](DyadicPoleFilter.lean) and [QuarticDualLine.lean](QuarticDualLine.lean). Each file prints its axiom dependencies. To replay the sixteen upstream proof files leading to the exclusion theorem, run the following from this snapshot, passing an Alpöge checkout at revision [ba2a065](https://github.com/Deicyde/riemann-hypothesis/tree/ba2a065656ec7c638baa601994de3e0245ff6665) with its matching mathlib cache. The script verifies the revision and reads the source bodies from Git.

~~~sh
python replay_landau_window.py /path/to/riemann-hypothesis
~~~

The [source hashes and axiom result](landau-sources.txt) identify the replay. The theorem requires both analytic data describing the poles of a transform and arbitrarily late passing windows for each positive exponent. We have finite Gaussian tests of the second requirement. The Riemann and rational Dirichlet statements in the external verification apply to the first two factors of the quartic field zeta. The new prime-window experiment concerns its third factor. The number of zeros of that factor in the two Dottie disks remains open. [Exclusion theorem and hypotheses](https://github.com/Deicyde/riemann-hypothesis/blob/ba2a065656ec7c638baa601994de3e0245ff6665/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83) · [MIT verification report](https://math.mit.edu/~drew/grh/)

### Reproducing the arithmetic

The scripts below run from this directory. The numerical checks used Python 3.12, python-flint 0.9.0, NumPy 2.5.5 and SymPy 1.14.0. The window integrals use 192-bit Arb arithmetic. The angular sum uses 224-bit Arb for the Gaussian weights, an 80-bit fixed-point truncation and exact integer accumulation. Both calculations include their error bounds. The class-group calculation used PARI/GP 2.20.0, with unconditional certification enabled.

~~~sh
python stirling_pell.py
python check_windows.py
python windows/prime_windows.py
python check_quartic_dual_theta.py
python angular/balanced_angular_theta.py
python angular/angular_eighth_power.py
python form_predictions.py
gp -q -f class_check.gp
~~~

The version-one deposit of November 21, 2026 collects the new derivations, forecasts and source checks. The small-window check imports the [archived Gaussian ideal enumerator](../2026-11-20-gaussian-reflected-disks-v001/gaussian_inputs.py). The longer window replay computes both descriptions of the prime signs directly. The factorial comparison uses the abstract of Prince Anand’s *The Arithmetic of the Brocard–Ramanujan Equation* supplied to this project. The fixed-order argument and the propagated Stirling error are derived in the linked note.
