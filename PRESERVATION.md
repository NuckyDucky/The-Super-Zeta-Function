# Depositing and preserving research

Use one new branch and one new snapshot directory per deposit. Name each snapshot `archive/YYYY-MM-DD-topic-vNNN` using a short lowercase topic and a three-digit revision. Once a snapshot lands on `main`, keep that directory immutable. Deposit corrections under a new revision and name the predecessor in the new snapshot README. Record the reason for the correction and which statements, precision claims or files it affects.

## Prepare a snapshot

1. Save the editable sources first. Include main notes, proofs, original data and computation source, generated evidence, and a README that identifies each entry point. Keep the original bytes whenever possible. Include any necessary exports alongside editable originals. Compare the selected files against the source inventory before staging.
2. Record the author or source, source date or revision, original relative filename, and any transformation. Where feasible, record the original SHA-256. For a rerunnable result, retain the exact command, interpreter and dependency versions, input and output references, parameters, units and branch conventions, precision, randomness settings where applicable, and sample or truncation limits.
3. Label evidence at the point of use. Identify **analytic proofs**, **exact symbolic or integer checks** with their finite scope, **directed numerical enclosures** with their rounding precision, **analytic bounds** on omitted terms, **point evaluations**, and **conjectures or open cases**. Give the enclosure, numerical value or explicit unresolved case when it matters.
4. Read the staged paths and diff. Keep this repository private. Include material you have permission to archive. Cite external material by canonical link and record relevant equations or page numbers. Keep credentials, private communications, unrelated files, generated environments, and identifying machine paths outside the deposit.
5. Generate the new snapshot's manifest after completing the content review. The manifest lists every file in the snapshot except itself. Run the integrity check and inspect the staged paths.

```text
python tools/verify_archive.py --write-manifest archive/YYYY-MM-DD-topic-vNNN
python tools/verify_archive.py
git diff --name-status --cached
git diff --check --cached
```

Snapshot files preserve their original bytes, including line endings. The repository's Git attributes enforce that behavior on checkout. The verifier checks both file inventory and hashes. Its `--base` option also checks for changes to earlier snapshot directories. The [GitHub Actions template](tools/github-actions/archive-integrity.yml) runs both checks against the base of pull requests and the preceding commit on ordinary pushes to `main` when installed at `.github/workflows/archive-integrity.yml`. Computational replay and math review remain separate evidence.

## Confirm the deposit

Open a pull request with the included checklist. Once merged, confirm the repository visibility is private, fetch the remote, and verify that the expected commit is on the remote default branch. Mark important milestones with an annotated tag. Keep the commit ID and tag in a separate recovery note. Avoid force pushes and moving preservation tags.

From a fresh clone, run `python tools/verify_archive.py` and open the research README. For computational work, replay in an empty scratch location and record outcomes, dependency versions, and any differences in evidence. A successful upload establishes one remote copy. Retain at least one verified offline copy on storage independent of your computer and GitHub account.

## Create and restore an independent copy

Run these commands from a fresh, verified clone. Give the bundle a unique filename and keep the hash with it. Create a new bundle for later milestones to retain the additional refs and objects.

```text
git bundle create ../super-zeta-YYYY-MM-DD.bundle --all
git bundle verify ../super-zeta-YYYY-MM-DD.bundle
```

On PowerShell, record the bundle checksum with `Get-FileHash ../super-zeta-YYYY-MM-DD.bundle -Algorithm SHA256`. Compare the checksum after copying the bundle to offline storage. Git bundles keep committed history and refs. Local edits, untracked files, and files stored outside Git require their own archive. If a future deposit uses Git LFS, preserve and verify its objects separately.

Recover to a new directory and run the same byte verification.

```text
git clone -b main super-zeta-YYYY-MM-DD.bundle super-zeta-restored
cd super-zeta-restored
python tools/verify_archive.py
git log -1 --format=%H
```
