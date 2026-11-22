# Reflected readings of the original spectrum, ordinary zeta and the Gaussian prefix

The center of the experiment is $w_0=1/2+i(T_D-1/512)$. For every plotted $w$, the corresponding spectral input is $s=w/2$. The outer measuring radius is $31/2048$ in $w$ coordinates and the inner one is $30/2048$. The crossed centers have real parts $31/64$ and $33/64$. The integers in the axes record displacement from $w_0$ in units of $1/2048$.

[Proof and both figures](../../docs/proofs/reflected-quarter-line.md) · [Lean theorem for the two disks](../../lean/SuperZeta/QuarterLine/QuarterReflectedReadings.lean) · [Injectivity of the original function](../../lean/SuperZeta/QuarterLine/QuarterOriginalUnivalent.lean)

| Reading | Evidence and scope |
| --- | --- |
| Original spectrum and ordinary Riemann zeta | [Fig. 1 and numerical method](side-by-side.md) · [Whole-rectangle enclosures and nine direct checks](side-by-side.json) |
| Original spectrum and Gaussian contribution through norm $2^{28}$ | [Fig. 2 and normalization](side-by-side-gaussian.md) · [Measured inputs](side-by-side-gaussian.csv.gz) · [Full remainder allowance and moment hash](side-by-side-gaussian.json) |
| Relative spectral magnitude at reflected points | [Bound on the entire disk](reflected-modulus-contrast.json) · [Contrast along the circumference](reflected-modulus-contrast.png) |
| Difference between the spectrum and its correction at exactly $T_D$ | [Three directed complex evaluations](reflected-readings.json) at the specified height. The disk figures use the slightly lower height $T_D-1/512$. |
| Signs in the ordered tower and clockwise angles at matched inputs | [Fixed-pair reconstruction](ordered-lift-audit.json) · [Fig. 3 and its derivative calculation](rotation-audit.md) · [Enclosures for all three angles](rotation-audit.json) |

Run the following from this snapshot directory with Python 3.12, python-flint 0.9.0, NumPy and Matplotlib. The Gaussian replay reads the existing signed moment archive and records its SHA-256. The code in this snapshot produces the figures and interval calculations. The full Gaussian circle count remains open.

```sh
python reflected-readings.py
python reflected-modulus-contrast.py --figure
python side-by-side.py
python side-by-side-gaussian.py ..
python ordered-lift-audit.py
python rotation-audit.py
```

Run `python tools/check_lean.py` from the repository root to build the spectral library and audit its theorem dependencies. The Lean proof uses the project's pinned Lean and mathlib 4.19.0. The decimal readings in the figures use Arb interval arithmetic. Base repository revision for this deposit is `b7d2c5cd5033d3976044da336f90a76e4204bd73`.

The local library build completed with all 23 new modules included. The project audit checked 1,824 theorem declarations against its foundational axiom list.
