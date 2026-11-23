# Dottie paired-score pilot

The pilot generates the exact candidate contributions for four Dottie paired-score rows and gives each row a Lean kernel proof. Each shard covers two rows under the squared norm cutoff 276,824,064. The published row numbers start at 1. In Lean, the corresponding span starts at the row number minus 1.

| Shard | Inclusive rows at the default setting | Width | Candidate records |
| --- | --- | ---: | ---: |
| 0 | 129–130 | 128 | 5 |
| 1 | 257–258 | 128 | 7 |

Each candidate CSV includes one head record per row, each full-width block, and any remainder. At the default setting, rows 130 and 258 end with one-term remainders. The replay checks the coverage, uses `decide +kernel` on each block and row assembly, and audits the resulting row theorem with `#print axioms`. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## GitHub Actions

The workflow runs two jobs on `ubuntu-24.04`. A pull request touching the workflow or runner uses the default rows. After the workflow is on the default branch, manual dispatch accepts a lower shard's first row from 129 through 896. The upper shard starts 128 rows later. Each job generates and checks its own candidates against the exact `lean-ideal73` source commit below.

The workflow uses the repository's checksum-verified elan install and Mathlib cache setup. It pins Lean 4.33.1 and Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. Each successful artifact contains the candidate CSV, generated Lean source and axiom logs, SHA-256 manifests for the source and output bytes, and a receipt with the shard's row bounds, toolchain, and theorem names. A failed job can upload its partial logs for diagnosis. The runner writes the successful receipt after both row proofs pass their audits.

## Local replay

Install Git, Node 24.19.0 and elan. From the checkout containing these tools, run the same two shards with fresh output directories.

```sh
git clone --depth=1 --filter=blob:none --no-checkout https://github.com/NuckyDucky/The-Super-Zeta-Function.git dottie-pinned-source
git -C dottie-pinned-source sparse-checkout set lean-ideal73
git -C dottie-pinned-source fetch --depth=1 --filter=blob:none origin ae1552ae1b5c1317e45b98bf5c2a805b85f39f50
git -C dottie-pinned-source -c core.autocrlf=false checkout --detach ae1552ae1b5c1317e45b98bf5c2a805b85f39f50
node tools/dottie-compute-pilot/run-shard.mjs dottie-pinned-source/lean-ideal73 ae1552ae1b5c1317e45b98bf5c2a805b85f39f50 dottie-receipts/shard-0 129 0
node tools/dottie-compute-pilot/run-shard.mjs dottie-pinned-source/lean-ideal73 ae1552ae1b5c1317e45b98bf5c2a805b85f39f50 dottie-receipts/shard-1 129 1
```

The runner verifies the raw source bytes against the requested Git tree, fetches the corresponding Mathlib cache, and builds the two Lean targets. The larger source manifest lists paths relative to the source checkout and, for the two `tools/` entries, the runner checkout. Run `sha256sum --check receipts.sha256` from an extracted shard to check its staged outputs.

To replay an existing CSV with the paired modules already built, use the original `node replay-paired-rows.mjs CHECKPOINT OUTPUT LEAN FIRST LAST WIDTH` interface inside `lake env`. `LEAN` is the absolute path to the compiler binary, `FIRST` and `LAST` are inclusive, and `WIDTH` must match the CSV's original block layout.

With the current `DottieStructuralPairBlocks` built, append `--lookup` to the replay command to use the exact faster sign evaluator. The pinned pilot currently uses the baseline path. Both paths prove the same row equalities. Run `lake env lean ../tools/dottie-compute-pilot/SignBenchmark.lean` from `lean-ideal73` to time the 256-position check.
