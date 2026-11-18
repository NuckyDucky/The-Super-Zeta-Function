# Reciprocal tetration, the Dottie spire, and the superzeta

Nick's original two papers and the first Lean formalization of the project are collected here. Start with the equation in the first paper, use the second to see the spire, and follow the [Lean theorem index](../../lean/README.md) to inspect the proofs.

| Read | Question |
| --- | --- |
| [Reciprocal Tetration in the Logarithmic Lift (PDF)](papers/foundations/main.pdf) · [TeX](papers/foundations/main.tex) | What happens when two exponential stages act in opposite order from the marked cap? |
| [The Dottie Parabolic Fold and the Marked Spire (PDF)](papers/dottie-spire/main.pdf) · [TeX](papers/dottie-spire/main.tex) | Where do the centerline phases meet, and which finite periods occur near the fold? |
| [Cosine spectrum and superzeta](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md) · [recent recovery results](../2026-11-18-superzeta-distance-v001/) | How do the phases give a determinant, rational traces and a Riemann reconstruction? |

The two papers include their editable source, bibliographies and every figure needed to typeset them. In either paper directory, run `latexmk -pdf main.tex` with a TeX installation. The supplied PDFs can be read independently.

## Results and their evidence

| Topic | What to open |
| --- | --- |
| Meme approximation and quadratic | [Lean proof](../../lean/SuperZeta/Meme.lean) of the exact inverse and signed gap. The separate [bounded search](checks/bounded_meme.py) and [certificate](checks/finite-optimum.json) cover the primitive integer vectors of height at most 936. See the [enumeration argument](notes/bounded-optimality.md). |
| Arithmetic of the resulting quartic | [Descent argument](arithmetic/research/hasse-obstruction.md), [local arithmetic checks](arithmetic/computation/verify_arithmetic.py) and [PARI record](arithmetic/computation/pari-replay.txt). The Lean theorem identifies the exact quartic polynomial. The Hasse conclusion uses the archived arithmetic descent. |
| Dottie centerline and finite spire | [Lean fold](../../lean/SuperZeta/Dottie.lean) and [period and trapping theorems](../../lean/SuperZeta/Reciprocal.lean). [Directed slice calculation](checks/dottie_slice.py) checks both ordered phases at both flanks and the midpoint. The finite witnesses establish capture there. The existence of two separated limiting horns remains open. |
| Fixed branches and continuation | [Response ODE](notes/response-flow.md), [Padé transfer](notes/pade-transfer.md) and [monodromy](notes/monodromy.md), with the [original replay programs and records](continuation/). The [Lean flow theorem](../../lean/SuperZeta/Flow.lean) derives the two differential equations from the local fixed equations. |
| Ordered coefficients, fields and radii | [Coefficient fields and functional independence](notes/coefficient-fields.md), [Hurwitz polynomial and order](notes/hurwitz-order.md) and [actual fourth derivative in Lean](../../lean/SuperZeta/Germ.lean). The transcendence and field-degree proofs remain in the mathematical notes. |
| Quartet scale and prime-adic dynamics | [Quarter shift](notes/quarter-shift.md), [Barnes normalization](../2026-11-16-super-zeta-v001/research/binomial-normalization.md), [prime-adic dynamics](../2026-11-16-super-zeta-v001/sources/foundation/padic-dynamics.md) and [Fatou clock](notes/fatou-clock.md). The [binary trace module](../../lean/SuperZeta/Binary.lean) states the precise formal-series identity needed for the all-index trace law. |
| Complex superzeta and zeros | [Vertical growth proof and interval checks](checks/complex_values.py), [formal spectral algebra](../../lean/SuperZeta/Spectrum.lean) and [formal recovery bounds](../../lean/SuperZeta/Recovery.lean). The first nonreal quartet dominates the full superzeta at high imaginary inputs. The canonical product and the Mellin reconstruction are written proofs at this release. |

## Replay the calculations

For the Lean verification, run `python tools/check_lean.py --fetch-cache` **from the repository root**. For the four experiments below, use Python 3.12 **from this snapshot directory**.

```sh
python -m pip install -r requirements.txt
python checks/complex_values.py
python checks/dottie_slice.py
python checks/binary_traces.py
python checks/bounded_meme.py --output replay-936.json
```

- The complex-value check uses 288-bit interval arithmetic and explicit integral-tail bounds. At $s=1/4+40i$ the first quartet mode alone has relative error about $1.59\times10^{-8}$.
- The spire replay uses 384-bit interval arithmetic at $\Im L=0.509892982511772$. The three scalar returns have primitive period 320. The contraction bounds are below $0.232$ at each flank and $7.43\times10^{-17}$ at the center.
- The binary replay checks exact rational traces through 128, then checks both spectra modulo $2^{32}$ through 65,536. Higher precision in the complex plane and higher 2-adic divisibility measure different properties of the same trace coefficients.
- The bounded search uses exact rational inequalities. Unimodular basis signs and elapsed time may differ by implementation. The winning primitive sign class and the enumerated candidates are reproduced.

## Provenance

The papers originate in Nick's revision v2.1 working sources. Both TeX files match the SHA-256 recorded when they were first deposited in the 2024-frontier working package. The referenced figures and compiled PDFs come from the matching manuscript directories. The mathematical notes, original replay scripts and saved records come from the project's meme, Dottie, 2024-frontier, quarter-shift, radius-selection, arithmetic and tetration-adic packages. In the reader copies, selected cross-references use repository-relative paths and two workstation paths were shortened to filenames.

The [manifest](manifest.json) records the bytes of every deposited file. The [project checksums](lean-source-sha256.json) identify the proof sources and pinned dependency manifest in the associated Git revision. For the distinction between a kernel theorem and an external certificate, see the [Lean index](../../lean/README.md).
