# From the reciprocal quartet to the determinant product

At unit coupling, I start with the squared roots of the multiplier-one equation for the ordered reciprocal exponential return. There is one Dottie square and a conjugate pair of squares at each positive quartet level. Lean proves that for every complex argument $v$ these roots determine the value of the determinant by

```math
E(v)=\prod_j\left(1-\frac{v}{\lambda_j}\right),
\qquad E(u^2)=\cos^2 u-u^2.
```

The [preceding enumeration](../2026-11-18-quartet-levels-v001/README.md) identified every simple zero and bounded the growth of $E$. The new proof divides out the enclosed zeros on expanding disks. The growth bound forces the remaining normalized factor to tend to one. This proves the product identity used in my [cosine-spectrum manuscript, §5](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md).

## What Lean checks

- `UnitSpectrum.determinant_product` proves the equality above for the roots selected by their defining equations. [Product proof](sources/DeterminantProduct.lean)
- `UnitSpectrum.root_hasSum` identifies the convergent sum over the actual squared roots on $1/2<\Re s<1$ with the continued super zeta. [Root sum](sources/UnitSpectrum.lean)
- `UnitSpectrum.difference_order` proves that the continued super zeta minus its Mellin correction has the same zero multiplicity as Riemann zeta at $2s$ throughout $0<\Re s<1/2$. [Multiplicity theorem](sources/UnitSpectrum.lean)

## Replay and provenance

The seven files under `sources/` preserve the November 18, 2026 Lean implementation byte for byte from the corresponding files under `lean/SuperZeta/` in this revision. The snapshot manifest records their SHA-256 hashes. The mathematical source is my cosine-spectrum manuscript linked above. The revision pins Lean 4.19.0 and the exact mathlib revision in the [Lake manifest](../../lean/lake-manifest.json).

From the repository root, run

```sh
python tools/check_lean.py --fetch-cache
python tools/verify_archive.py
```
