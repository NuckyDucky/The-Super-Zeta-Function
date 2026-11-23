# Packed production replay

The production workflow checks rows 513–16,638 with width 1,024 on Ubuntu 24.04. It uses the existing packed-witness replayer once per row, with 36 contiguous weighted jobs and at most 18 active at a time. The planner records 108,563,533 paired positions and a linear estimate derived from 51.9001127 seconds for row 11,000. Runtime receipts hold measured seconds.

## Authorize one run on an open draft pull request

Apply the overlay at the repository root and commit it on the open draft's same-repository head branch, together with the intended pinned Lean sources. This is the proof commit and must include the Lake target `DottieWitnessPairBlocks` and its dependencies. The overlay contains the workflow but leaves the marker creation to the person authorizing the run.

From that proof commit, use one marker-only commit. The following example is for Bash.

```sh
proof_sha=$(git rev-parse HEAD)
printf '{"replay":"packed-witness-513-16638-v1","proofCommit":"%s"}\n' "$proof_sha" > .github/dottie-packed-production.json
git add -- .github/dottie-packed-production.json
git commit --only -m "Authorize the packed Dottie production replay" -- .github/dottie-packed-production.json
git push
```

The marker commit's sole parent is the immutable proof SHA. The workflow fires on the draft PR's `synchronize` event. The gate checks the exact PR head, marker-only diff, replay identifier, and parent SHA. Replay jobs run only on the first attempt. Unrelated pushes with the old marker in their ancestry skip production. The trigger relies on a normal PR update from an authorized push.

## Retrieve the assembly inputs

After the run succeeds, download its plan and 36 shard artifacts by run ID.

```sh
gh run download "$RUN_ID" --pattern 'dottie-production-*' --dir production
node tools/dottie-compute-pilot/collect-packed-receipts.mjs production > packed-assembly-inputs.json
```

The plan artifact records both immutable SHAs and the complete matrix. Each shard records its candidates, source hashes, row ticks, generated `.lean` and compiled `.olean` files, individual logs, named axiom receipts, and SHA-256 hashes. Its `receipt.json` measures runner setup including the Mathlib cache and module build, candidate generation, and the packed Lean replay. Use the workflow's job elapsed time to include checkout, toolchain installation, and artifact upload. The replay step has a 335-minute cap within the 360-minute job so artifact collection can finish.

The collector checks the exact matrix, contiguous row metadata, per-file digests, consistent source manifests, and the allowed axioms for each row. It fails on a missing or partial shard. Its ordered output supplies the (513)–(16638) theorem names, imports and integer ticks, together with the candidate tail sum.

Assemble under Lean 4.33.1 and the matching pinned package dependencies. Put each downloaded `kernel` directory on `LEAN_PATH` for the compiled inputs, or rebuild the corresponding generated sources under that same pin. Combine consecutive spans with `dottiePairedRowSpan_add`, then prepend the separately audited `QuarticModel.dottiePairedRows_1_512` from `DottiePairedRowsThrough512.lean` and its imports. Use `dottieQuickReferenceScore_eq_row_span` to transfer the checked full span to the exact score. The final numerical comparison is `7 * (2^48)^5 < 50 * S` for the checked full integer sum `S`. Audit the assembled theorem with `#print axioms`.
