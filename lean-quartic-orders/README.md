# The quartic theta kernel in the two quaternion orders

The input is a point in the right Dottie annulus. Its original super-zeta address indexes a quaternion whose first complex component is the completed Gaussian reading and whose second is the Dirichlet total. Exchanging the order of the two Hamilton units gives two complex coordinates to measure at that same input. The calculation in [QuarticSignedOrders.lean](QuarticSignedOrders.lean) expresses the difference using the signed theta kernel of the fixed quartic.

## Where the sign enters

The conductor is $D=41\cdot457\cdot1{,}414{,}835{,}497=26{,}509{,}772{,}707{,}289$. The Lean sources construct its real primitive even character. Murphy proves that every real primitive Dirichlet character has root number $+1$. The Lean 4.19 port applies his theorem to this character and proves the Gauss amplitude is the positive square root of the conductor. This establishes the theta reflection at every positive scale, independently of the numerical grid. [Primitive character](QuarticPrimitive.lean) · [Murphy’s sign theorem, v1.0.0](https://github.com/DrMurphyIsIn/real-dirichlet-dbn-lean/blob/v1.0.0/lean/gauss/GaussSign.lean#L281-L287) · [Specialization in Lean 4.19](QuarticConductorSign.lean) · [Ported sign theorem](GaussSign.lean) · [Upstream notice](murphy-license/UPSTREAM-NOTICE.md) · [Source license](murphy-license/LICENSE)

## Reading the two orders

For $w=\tfrac12+a+it$, let $K$ be the quartic's real theta kernel on the logarithmic scale. Reflection with positive sign folds the Mellin integral into two coordinates,

$$
C(a,t)=2\int_0^\infty K(u)\cosh(au)\cos(tu)\,du,\qquad
S(a,t)=2\int_0^\infty K(u)\sinh(au)\sin(tu)\,du.
$$

Write $G=C+iS$ for the full Mellin reading. At its super-zeta address, the quaternion difference $jQk-kQj$ has real coordinate $2S$ and $i$ coordinate $2C$. The other two coordinates vanish. Knowing the two orders therefore recovers the complete complex reading at that input. Proving that the orders differ everywhere in the right ring requires ruling out a simultaneous zero of these two integrals there. [Coordinate calculation](QuarticSignedOrders.lean) · [Hamilton multiplication and inverse](QuarticOrderedTurns.lean)

The control uses three positive masses. Given an offset $a$ and a positive target height $T$, put $b=\pi/T$. Masses of $1/2$ at $\pm b$ and $\cosh(ba)$ at $0$ give the entire transform $\cosh(bz)+\cosh(ba)$. Its reflection has the positive sign, and its values at $z=\pm a+iT$ are exactly zero. The control retains distinct super-zeta addresses for those two inputs. The quartic calculation uses its own signed coefficients in $K$. [Three-mass control](OrderedSignControl.lean)

## Reproduction

From the repository root, with Python 3 and elan installed, run

```sh
python lean-quartic-orders/replay.py --fetch-cache
```

The command uses the toolchain and package lockfile in `lean/`. It follows imports from the signed-order theorem, recompiles the repository sources in a temporary directory, and checks the transitive axiom dependencies of every theorem in those modules against `propext`, `Classical.choice`, and `Quot.sound`. The replay includes the eight adapted modules from Peter W. Murphy’s v1.0.0 release. The root number is derived in the same build as the ring equivalence. A second checkout with the identical lockfile and toolchain can supply the mathlib cache through `--lake-project /path/to/checkout/lean`.
