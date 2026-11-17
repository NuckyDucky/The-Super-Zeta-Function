# Super Zeta continuation

Research date 16 November 2026. First deposit of the Greater Works continuation package.

- [Connected narrative](Greater-Work.md) develops the argument from reciprocal spectral inputs to shifted superzeta residues, elliptic periods, Barnes normalization, inverse-branch and prime-clock traces, ordered parabolic histories, and the Laplace–Barnes expansion.
- [Formula-specific source map](source-map.md) identifies the public references, retained reciprocal inputs and additional derivations.
- [Verification record](verification-record.md) describes the original evidence, including exact checks, directed numerical enclosures, analytical tails and high-precision point evaluations. This archive also retains the substantive proof and numerical reviews under `review/`.
- [Provenance](provenance.json) records the SHA-256 of the original delivery ZIP and of each selected source file. Most files retain their original bytes. The recorded archive edits are attribution, link and path changes. The original delivery and earlier packages provide the wider context.

## Replay in a scratch directory

Use Python 3.12 and install the recorded numerical dependencies in an environment dedicated to this replay. From the repository root, run the commands below. The replay destination must be new. The original evidence remains in this snapshot, and the replay saves its outputs and figures in the scratch copy. The original delivery's broader package audit covered local source mirrors and packaging; this archive uses its own integrity check.

```text
python -m pip install -r archive/2026-11-16-super-zeta-v001/requirements.txt
python tools/replay_super_zeta.py ../super-zeta-replay
python tools/verify_archive.py
```
