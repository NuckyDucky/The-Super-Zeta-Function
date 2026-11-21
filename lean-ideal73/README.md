# The quartic field at 73

This package constructs the field $E=\mathbb Q(i,\sqrt{-5045155+1027708i})$ and recovers it from the root of the original quartic. The norm in the theorem is mathlib’s absolute ideal norm in the ring of integers of this field. There are exactly two integral ideals of norm 73. They both have residue $i=46$ in $\mathbb F_{73}$, with the square root of the discriminant reducing to 9 or 64. The other prime above 73 has residue degree two and norm 5329.

| Source | Step proved |
|---|---|
| [Original quartic branch](OriginalQuarticBranch.lean) | The root of the Gaussian quadratic generates the same rational field. |
| [Integral field model](QuarticModel.lean) | The monic quartic for the integral generator is irreducible and is its minimal polynomial. |
| [Good reduction](GoodPrime.lean) | The order exponent is prime to 73, so reduction of the minimal polynomial detects the maximal order. |
| [Prime-norm coefficient](PrimeIdealCoefficient.lean) | Ideals of prime norm correspond to residue maps. At a good prime their number equals the number of roots of the reduced polynomial. |
| [The actual count](QuarticAt73.lean) | Mathlib’s subtype of ideals of this field with norm 73 has cardinality two. |
| [All primes above 73](PrimeDecomposition73.lean) | The three specified primes exhaust the list. All are unramified, and their residue degrees are 1, 1 and 2. |
| [Ideals of every power of 73](PrimePowerIdealCount.lean) | Unique factorization identifies the ideals of norm $73^n$ with triples $a+b+2c=n$. The even and odd formulas count these actual ideals. |

Run the following commands from this directory with elan installed. The toolchain file selects Lean 4.33.1. The lockfile pins mathlib and its dependencies. The first command obtains the compiled mathlib imports. The second builds the field modules and checks the principal theorems’ transitive axiom dependencies against the three foundational axioms allowed by the project.

~~~sh
lake exe cache get Mathlib.Tactic Mathlib.NumberTheory.NumberField.DedekindZeta Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind Mathlib.RingTheory.DedekindDomain.Different Mathlib.Algebra.Polynomial.Eval.Irreducible Mathlib.RingTheory.Polynomial.GaussLemma
lake build
~~~

The [spectral library](../lean/README.md) uses its own pinned Lean 4.19 toolchain. For the comparison of its corrected trace with the field’s ideal-counting series, see [the proof and independent PARI calculation](../docs/proofs/gaussian-ideals-and-super-zeta.md). With PARI/GP on the path and python-flint installed, run the comparison from the repository root.

~~~sh
python -B tools/check_quartic_ideal_series.py
~~~
