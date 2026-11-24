# Dottie score verification

Lean checked the exact integer reference score from all 37 partitions covering rows 1–16,638. The join used one CPU worker and peaked at 6.68 GiB of private memory. The final source and transitive `#print axioms` output are here. The row proofs come from the pinned production replay and the checked prefix. [Join](DottieProductionJoined.lean) · [Join arithmetic](DottieProductionJoinOnly.lean) · [Audit](DottieProductionScore.audit.txt) · [Production row receipts](https://github.com/NuckyDucky/The-Super-Zeta-Function/actions/runs/45210378405)

To replay the join, use Lean 4.33.1 and the mathlib pinned at `0df444a360eaa60ab8c11dca51a86af692955474`. Put the checked production partitions and the checked prefix on `LEAN_PATH`. Use the packed proof for `DottiePairedRows497Through512` and the production copies of rows 1025 and 1054. Build the join arithmetic and joined score in that order, then run the audit source. [Audit source](DottieProductionAudit.lean) · [Original proof revision](https://github.com/NuckyDucky/The-Super-Zeta-Function/tree/bb333dc2511ba979a53f19b14f4212ab3f198bc3)

## Save a running worker’s results

Set `DOTTIE_CHECKPOINT_SPOOL` to a writable folder in the worker’s environment. `replay-paired-rows.mjs` adds the Lean source, compiled object, and axiom log to that folder after each successful batch. One uploader can share the spool with the workers on its machine. It checks every three minutes and verifies GitHub’s SHA-256 before clearing a queued archive. A failed upload leaves the archive queued.

Create a draft release in your private backup repository, then start the mirror with Node 24 and an authenticated GitHub CLI.

```sh
export DOTTIE_CHECKPOINT_SPOOL="$PWD/.dottie-checkpoint-spool"
node tools/dottie-compute-pilot/checkpoint-results.mjs mirror "$DOTTIE_CHECKPOINT_SPOOL" owner/private-backups dottie-run-01 --watch
```

In PowerShell, set the same variable with `$env:DOTTIE_CHECKPOINT_SPOOL = "$PWD/.dottie-checkpoint-spool"`. Keep that value in each worker’s environment as well as the uploader’s.

Run the same command without `--watch` to flush once when workers finish. Download a checkpoint asset from the draft release and restore it into the worker’s output folder. The restore checks both the archive and its files. It accepts existing files with matching bytes and stops at a conflict.

```sh
node tools/dottie-compute-pilot/checkpoint-results.mjs restore lean-checkpoint-HASH.json.gz worker-output
```

Start the replay at the next unfinished row under the same Lean and mathlib pins. A completed batch typically waits at most three minutes for the next upload attempt. Time inside an unfinished Lean batch and time during a network outage are separate.

## Help with the next verification

Independent replays of a bounded range are welcome. Include the source revision, row range, Lean version, and `#print axioms` output in your pull request so someone else can compare the exact declarations. The next signed-tail calculation concerns the right measuring circle at the same archived Dottie input. A check of one arc with a rigorous error bound would give us a result to compare before we expand the range. [Production replay](../../tools/dottie-compute-pilot/ASSEMBLY.md) · [Signed-tail statement](../../lean-ideal73/DottieShorterOmittedBudget.lean)
