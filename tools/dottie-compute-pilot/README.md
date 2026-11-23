# Dottie packed-witness pilot

The two Ubuntu jobs each check two complete rows of the original paired Gaussian score. The default rows are 11,000–11,001 and 11,128–11,129. Both jobs use 1,024 positions per block and a single Lean worker. Manual dispatch accepts a lower starting row from 1 through 16,509.

The candidate producer emits the original exact integer targets. The Node generator supplies modular roots in both orientations, using two 32-bit words per position. Lean unpacks the words, checks each needed modular square, and proves the same row equalities as the original evaluator.

The workflow pins the [Lean sources](https://github.com/NuckyDucky/The-Super-Zeta-Function/tree/163f2bc23c88d7bb7c5862cdd2132fe900f9231f/lean-ideal73), Lean 4.33.1, and the Mathlib commit in the Lake manifest. Successful artifacts contain the generated sources, candidate CSV, axiom logs, and SHA-256 manifests. The expected axiom list is `propext, Classical.choice, Quot.sound`.

To replay a pilot job, run the following from the checkout containing this runner. Set the first argument to the pinned Lean package directory and use a fresh output path.

```sh
node tools/dottie-compute-pilot/run-shard.mjs .dottie-source/lean-ideal73 163f2bc23c88d7bb7c5862cdd2132fe900f9231f dottie-receipts/shard-0 11000 0
```

With the Lean modules built and the pinned environment loaded, the existing candidate CSV can be replayed directly.

```sh
node tools/dottie-compute-pilot/replay-paired-rows.mjs CHECKPOINT OUTPUT LEAN FIRST LAST WIDTH --witness
```

Use the archived block width when reusing a checkpoint. The optional `--bundle` flag checks several consecutive rows in one Lean module. The pilot emits separate row modules and receipts. The packaged benchmark source checks both exact scores and a deliberately corrupted root.

