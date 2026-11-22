# Gauss's sign in Lean 4.19

These eight modules adapt the sign proof from [Murphy's v1.0.0 release](https://github.com/DrMurphyIsIn/real-dirichlet-dbn-lean/tree/b0a613a65bfafb30774c6fe7ef05934720644b23/lean). The upstream license and notice are reproduced in `LICENSE` and `UPSTREAM-NOTICE.md`.

`GenThetaFE` supplies three general lemmas used by the sign proof. `GenChi4` supplies the calculations for the character modulo four. `GaussQuad`, `GaussPrime`, `GaussCRT`, `GaussPow`, `GaussTwo`, and `GaussSign` establish the quadratic sum, evaluate primitive characters at odd primes and powers of two, and combine their root numbers. The final declaration is `DBN.Gen.rootNumber_eq_one_of_real_primitive`.

The port uses specific mathlib imports and adapts proofs to the 4.19 interfaces for limits, roots, conductors and field simplification. The heat-flow corollaries are omitted. The estimate for `‖exp (I * x) − 1‖` in `GaussQuad` adapts two mathlib proofs from commit `0df444a360eaa60ab8c11dca51a86af692955474`, under Apache 2.0.

- [Mathlib.Analysis.Complex.Trigonometric](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/Trigonometric.lean#L973). Copyright (c) 2018 Chris Hughes. All rights reserved. Authors include Chris Hughes and Abhimanyu Pallavi Sudhir.
- [Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean#L260). Copyright (c) 2022 David Loeffler. All rights reserved. Authors include David Loeffler, Yaël Dillies and Bhavik Mehta.

The modules compile in this order with Lean 4.19.0 and mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```text
GenThetaFE  GenChi4  GaussQuad  GaussPrime  GaussCRT  GaussPow  GaussTwo  GaussSign
```
