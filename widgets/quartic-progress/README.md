# Quartic verification widget

The Stage 2 star shows the height, reflection, and Hamilton axis steps. Open **Stage 1 and research galaxy** to see the checked coefficient batches, prefix blocks, and interval enclosures. The [quartic verification packet](../../verification/quartic-kernel/README.md) contains the Lean replay.

## Archived snapshot

Serve this directory as static files and open `index.html`. The page loads the bundled [progress record](progress.json) once and shows its capture time. The record contains **6,705 / 6,705** coefficient batches, **181 / 181** prefix blocks, and **66 / 66** enclosure modules. The recorded full replay built **95** modules against **7,008** checked certificate modules and audited the kernel theorem with `propext`, `Classical.choice`, and `Quot.sound`.

The separate low-height check verified the imaginary readings at height `1/4` and horizontal offsets `-1/100`, `0`, and `1/100`. The outer readings have opposite values. The next Stage 2 check is a whole-ring lower bound on `j² + k²` on the right. Covering the candidate domain is a separate milestone.

From the repository root, run a static preview as follows and visit [the local preview](http://127.0.0.1:8767/).

```sh
python -m http.server 8767 --bind 127.0.0.1 --directory widgets/quartic-progress
```

The browser uses WebGL2 for the batch grid when available and Canvas 2D otherwise. The CSS, JavaScript, and JSON load from the widget directory. The same directory can be served at a subpath alongside the existing [Hurwitz paths](https://nuckyducky.github.io/The-Super-Zeta-Function/) and [two-input spectral map](https://nuckyducky.github.io/The-Super-Zeta-Function/two-input/).

## Live localhost view

After generating the certificate sources, run the Python standard-library server from the repository root and visit [the live view](http://127.0.0.1:8766/).

```sh
python widgets/quartic-progress/serve.py
```

The server reads `verification/quartic-kernel/.replay/`. It takes its module names and cell ranges from `generated/`, reads the grid spacing from `verification/quartic-kernel/source/QuarticGrid.lean`, displays checkpoints from `certificate/`, and reads the two transcripts `certificate.log` and `full.log`. A checked module has both a saved receipt and a compiled artifact. Module names and interval ranges in the bulletin come from the replay record.

Use `--packet`, `--checkpoint`, `--kernel-log`, and `--replay-log` for another layout. Use `--replay-build-root` for the directory containing the full replay build and `--grid` to override the grid source. `--freeze PATH` saves a new snapshot instead of opening the server.

The live view listens on loopback and serves the interface plus summary data. Replay directories and transcripts stay local. The widget displays the evidence from the replay commands in the verification packet.
