# The Dottie clocks and the moving Hurwitz plane

I studied two experiments near the sixth Riemann zero. In the first, I turned the Hurwitz shift and followed the deformation of the surrounding plane. In the second, I held the shift fixed and changed the continuous path by which the Dottie multiplier acts on the value of the function.

| What I hold fixed | What I vary | What the data answer |
| --- | --- | --- |
| The starting value of the symmetrized Hurwitz sum | Its shift, from the trough to the landing | The derivative tells me how much a small neighborhood shrinks, rotates or expands. [Plane map](atlas/plane_notes.md) |
| The endpoint function and its one-lap multiplier | The logarithm of that multiplier used over the lap | Two logarithmic lifts take the same disk of starting points to different zeros. [Ordered stages, logarithms and inverse branches](atlas/THESIS.md) |
| A particular moving zero and a specified remaining angle | The order and update frequency of a local forecast | The derivative and acceleration give measurable improvements in complex endpoint error on known tracks and two newly tested seeds. [Ten-track comparison](landing/README.md) · [Preregistered two-seed test](holdout/README.md) |

The basin result holds for every point within $10^{-6}$ of $37i$. With the principal logarithm the destination is $8\pi i/\log 2$. With the logarithm obtained from the ordered exponential stages it is Riemann zero six. I followed both inverse branches to the same simple critical point and determined their opposite square-root signs. The surrounding basin image is a numerical survey. The small starting disk, both limits and the branch identification have separate directed proofs. [Starting-disk proof](atlas/basin_certificate.json) · [Critical value inside the loop](atlas/critical_loop.json) · [Two signed branches](atlas/critical_branches.json)

The first diagram measures final length divided by starting length for a very short segment. A value of $1/2$ halves it and a value of $2$ doubles it. The second diagram plots every resolved endpoint, including points outside the original rectangle. [Length change across the plane](atlas/plane_strain.png) · [Entire starting and final grids](atlas/plane_grid.png)

I measured a wider rectangle using 38,801 starting positions. The original closeup has 37 flagged samples. I followed each of those exact grid centers with directed arithmetic and verified all their endpoints. In every one of the 37 squares I also isolated a different source position whose level reaches a moving critical value. All 37 paths reach the same branch from its negative square-root sheet. [Proof of the 37 folds](atlas/gray_collision.json) [Wide view](atlas/plane_wide.png) · [Verified centers](atlas/staircase.json) · [Critical levels in the squares](atlas/gray_locus.json)

After scoring the two new seeds, I measured the same ratio over their whole turns. Seed 7 expanded by a factor of $1.18120$, while seed 8 shrank to $0.51124$ of its starting length. Both expanded slightly over the final eighth of a degree. [Length and angle at both seeds](holdout/local_scale.json)

## Reproduce the experiments

Use Python 3.12 with the pinned dependencies. From the repository root, the following commands stage fresh outputs, check the source of the sixth-branch overlay, regenerate both maps and replay the masked forecasts. The new-seed work can be replayed in its four original stages using its own instructions. [Two-seed commands and hashes](holdout/README.md) · [Public pre-evaluation commit](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/a739bf30c0db09774d4fd3681596a1821f31d081/protocols/2026-11-19-dottie-plane-holdout.json)

~~~sh
python -m pip install python-flint==0.9.0 numpy==2.5.5 matplotlib==3.11.2
python -B tools/replay_plane_atlas.py
python -B archive/2026-11-19-dottie-plane-atlas-v001/landing/replay.py --geometry --backward
python -B tools/replay_single_term.py
~~~

Both maps use step-size comparisons as numerical acceptance criteria. Their companion scripts provide directed enclosures at the named witnesses. The retrospective study uses the known first ten landings. The next two seeds were selected by consecutive index in a public commit before I computed either path. The cutoff family rule and quadratic error target were fixed in that commit. The ordinal of the Riemann landing came from comparing the final disk with a zero isolator after the prediction. [Retrospective protocol](landing/Dottie-Blind-Landing/protocol.json) · [Forward-test protocol](holdout/protocol.json) · [Scores](holdout/score.json)

The one-term inverse from the preceding snapshot now also has a stricter regression check. It rereads the output intervals at 768 bits, tests the real and imaginary parts of both marked phases and of the multiplier, and compares the exact rational enclosures of the recovered parameter. A fresh interval must overlap its published interval and have radius no larger than $5/4$ of the published radius. That last factor is the regression tolerance. The generating proofs retain their original working precisions. [Earlier inverse](../2026-11-19-single-term-inverse-v001/README.md) · [Improved comparison](../../tools/replay_single_term.py)

NuckyDucky, 19 November 2026. The numerical work uses Fredrik Johansson's Arb, FLINT and python-flint. McPhedran, Botten and Nicorovici gave the equation of motion for zeros of the symmetrized Hurwitz sum. The original reciprocal orbit and trace calibrations are cited at their points of use. [Hurwitz zero trajectories, §3](https://doi.org/10.1098/rspa.2006.1763) · [Arb](https://doi.org/10.1109/TC.2017.2690633) · [Source and transfer record](provenance.json)
