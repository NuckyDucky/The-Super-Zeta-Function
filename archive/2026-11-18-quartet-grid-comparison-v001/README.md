# What changes when I replace the quartet radii with a grid?

The corrected second audit asked which part of my factorial result comes from counting balanced sign histories and which part requires my quartet radii. I compare the two sequences at the same integer level, using the same factorial weight. Both displacements approach $1/4$. Only the sequence using the actual radii crosses the lower zero of the Hurwitz value, between levels 28 and 29. [Earlier proof for the quartet levels](../2026-11-18-lean-foundations-v001/notes/quarter-shift.md#1-global-discrete-theorem) · [Corrected audit notebook](super_zeta_second_adversarial_audit_corrected.ipynb)

## The comparison

I use $B_n=4^{-n}\binom{2n}{n}$, $D_n=\pi n B_n^2$, and the actual quartet radius $R_n$. The grid substitutes $2\pi n$ for $R_n$. The difference between the displacements is exact.

```math
\delta_n^{\mathrm{grid}}=n(1-D_n),\qquad
\delta_n=\delta_n^{\mathrm{grid}}-\frac{D_n}{2\pi}(R_n-2\pi n).
```

The binomial factor gives the grid limit $1/4$. The quartet equations give $R_n-2\pi n\to0$, which carries the same limit over to the actual spectrum. At finite levels the radial difference matters. The lower zero of $H(\delta)=\zeta(-1,1-\delta)=-1/12+\delta/2-\delta^2/2$ is $\delta_c=(1-1/\sqrt3)/2=0.211324865405187\ldots$. [Binomial proof](../../lean/SuperZeta/Barnes.lean) · [Quartet-radius proof](../../lean/SuperZeta/QuartetRadius.lean) · [Hurwitz special value](https://dlmf.nist.gov/25.11.E14)

| Level | Actual displacement | Grid displacement | Sign of $H$ (actual / grid) |
| ---: | ---: | ---: | :---: |
| 1 | 0.1566414985 | 0.2146018366 | − / + |
| 28 | 0.2110943522 | 0.2488740794 | − / + |
| 29 | 0.2118561136 | 0.2489132283 | + / + |

For the actual spectrum, the sign is negative for every level from 1 through 28 and positive at every level from 29 onward. The crossings discussed here concern the real Hurwitz value at order $-1$. [Directed results for the first 127 levels and the bound from level 128 onward](computations/global-quarter-shift-results.json)

### Why the grid stays above the threshold at every level

The reviewer supplied a short proof using the exact binomial kernel. For $a>0$, write $q=e^{-a}$. Then $\tanh a-(1-e^{-a})=q(1-q)^2/(1+q^2)>0$. Substituting $a=t/4$ in the kernel gives

```math
-\log D_n=\int_0^\infty e^{-nt}\frac{\tanh(t/4)}{t}\,dt
>\int_0^\infty \frac{e^{-nt}-e^{-(n+1/4)t}}{t}\,dt
=\log\frac{4n+1}{4n}.
```

Thus $D_n<4n/(4n+1)$. The exact binomial recurrence $D_{n+1}/D_n=1+1/[4n(n+1)]$ now gives, for $n\ge1$,

```math
\delta_{n+1}^{\mathrm{grid}}-\delta_n^{\mathrm{grid}}
=1-D_n\left(1+\frac{1}{4n}\right)>0.
```

At the first level $\delta_1^{\mathrm{grid}}=1-\pi/4>\delta_c$. Every later level lies above it, and the limit is $1/4$. Lean checks strict increase and the exact threshold inequality via a second proof using Wallis bounds. The theorem names are `grid_displacement_strictMono` and `grid_displacement_gt_hurwitz`. [Lean source](../../lean/SuperZeta/Barnes.lean) · [Binomial kernel](../2026-11-16-super-zeta-v001/research/binomial-normalization.md)

## Where the counting choice enters

At the Dottie parameter I select four inverse branches of the exponential return, assign them the four unit lattice directions, and count the marked words equally. The fraction with total charge zero in $2j$ steps is exactly $B_j^2$. With one pair of steps, for instance, each of the four directions has one opposite, so four of the sixteen ordered words balance. The equations certify that these four branches exist. I choose the branches, their charges, their equal weights, and finally $j=n$ when I use the resulting count at quartet level $n$. The cap itself follows the two prescribed alternating exponential stages. [Exact counts and dynamical realization, equations (5) and (15)–(17)](../2026-11-16-super-zeta-v001/research/balanced-charge-operators.md) · [768-bit branch certificate](../2026-11-16-super-zeta-v001/computations/balanced-charge-results.json)

## Reproduction and source record

- The [corrected second audit](super_zeta_second_adversarial_audit_corrected.ipynb) is the supplied notebook in its original bytes. It uses SymPy 1.14.0 and mpmath 1.3.0, independently of the repository's computation code. Run all five code cells. They check the quartet and grid displacements, inverse-branch bounds and eight finite determinant polynomials. The reviewer withdrew the matrix objection after reading the denominator in the [deposited projection](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md#3-exact-fredholm-determinant-and-controlled-finite-matrices). At $N=2$, $\varepsilon=2$, $u=1$, the source matrix gives $1/8$.
- The [quartet verifier](computations/verify_global_quarter_shift.py) and its [original output](computations/global-quarter-shift-results.json) come from my earlier *Greater Works — Quarter Shift* computation. They preserve the source bytes under their original filenames. To replay, copy the verifier to a scratch directory and run `python verify_global_quarter_shift.py` there with Python 3.12.11, python-flint 0.9.0 and mpmath 1.3.0. It writes a fresh JSON file. The 512-bit calculation uses 360 rational bisections per level. All fields except elapsed time matched the deposited result. The [written tail argument](../2026-11-18-lean-foundations-v001/notes/quarter-shift.md) covers every level from 128 onward.
- From the repository root run `python tools/check_lean.py` with the pinned Lean 4.19.0 toolchain. The two new Lean theorems concern the grid. The evidence for the actual quartet transition combines the analytic tail proof and directed interval arithmetic. The snapshot manifest records the hashes of the notebook, verifier and output.
