# Hosted packed proof assembly

Apply this overlay to the same open draft PR as the packed production replay. The checkout needs the production collector, weighted planner, packed row replayer, and witness generator already staged by that replay. The proof commit itself needs the pinned Lean and Mathlib package with the witness, candidate, and score modules.

After the production run succeeds, authorize assembly with a marker-only commit creating `.github/dottie-packed-assembly.json`. Use the production run ID, its exact event head and the proof commit selected by that head.

```json
{
  "assembly": "packed-witness-full-assembly-v1",
  "productionRunId": 45210378405,
  "proofCommit": "bb333dc2511ba979a53f19b14f4212ab3f198bc3",
  "activationCommit": "1a0fc12cbaf2b33dcf8b7db711fa08355a252b4d"
}
```

Commit the workflow and tools first. Commit only the marker next and push the same-repository branch to raise the draft PR's `synchronize` event. The gate reads the exact run through the Actions API, requires a successful first-attempt production run at the given activation commit, and verifies that the activation's sole parent matches the proof commit. The pinned download action uses its own repository token with `actions: read`.

The collector validates all 36 shard receipts and both SHAs before proof setup. Lean rebuilds the matching proof dependencies on Ubuntu. Rows 1–512 are regenerated at width 1,024 and kernel-checked in 32 packed modules of 16 rows. That prefix covers 130,816 paired positions and its aggregate must match the audited integer. This keeps the prefix proof reproducible from the pinned sources and saves uploading local generated rows.

Each assembly module compiles serially with warnings as errors. The resulting artifact contains the final Lean source and olean, prefix source, build manifest, kernel audit, phase timings, per-module peak RSS readings, and hashes in `proof-receipt.json`. The downloaded production receipts and reproducible intermediate assembly modules provide the corresponding dependencies for the compact artifact.

The Windows source-rebuild utility in the production overlay accepts `COLLECTOR_JSON DOWNLOAD_ROOT LEAN_PROJECT OUTPUT FIRST LAST`. Prepare the pinned local proof checkout and build `DottieWitnessPairBlocks` first. It checks each downloaded source hash, compiles one row at a time, audits the declared theorem, and writes separate native oleans. The output mirrors the input artifact layout so the assembly generator can take it as its row import root.
