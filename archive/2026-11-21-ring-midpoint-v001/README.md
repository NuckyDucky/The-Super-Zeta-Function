# Half the Dirichlet total in the right ring

I fix the quartic and a single input. I use the two analytic identities for its Gaussian factor and its continued ideal-class sums as premises. The tower supplies a separate measured quantity, the cap derivative ratio for a chronological word. The [Lean proofs](../../lean/SuperZeta/GaussianRingMidpoint.lean) check the consequences of these premises at that same input. The [arithmetic derivation](../2026-11-21-quartic-projections-v001/fields-and-windows.md) identifies the functions for the quartic.

At a Gaussian zero, Lean derives both midpoint equalities. Applying the order theorem then leaves one equality between derivative ratios to prove. In [the recorded proof state](ProofState.lean), `h₀`, `h₂` and `he` are already available. The line beginning with `⊢` is the remaining goal. The guard makes Lean reproduce the diagnostic. The module also proves that the proposed transfer of equality, quantified over this open annulus, is equivalent to Gaussian zero exclusion there.

I used the existing right center $33/64+i(T_D-1/512)$ and the open radii $30/2048$ and $31/2048$. The field sums use the ring input $w$. The derivatives are with respect to the starting cap and evaluated at $1$, at a fixed lift $m\pi i$ with nonzero integer $m$. Identifying these two measurements from the quartic arithmetic remains open.

## Replay

From the repository's `lean` directory, with its pinned Lean 4.19.0 and mathlib dependencies, run

```sh
lake build SuperZeta.GaussianRingMidpoint
lake env lean ../archive/2026-11-21-ring-midpoint-v001/ProofState.lean
```

The successful diagnostic replay means the supplied proof attempt has the displayed open goal. The separate theorem `transport_iff_ring_clear` proves the logical equivalence. The project audit includes all six theorem declarations. This snapshot records the same-input calculation on November 21, 2026, building on the quartic projection identities at repository revision `b7d2c5c`.
