# Two-height pilot

I included the original [protocol](protocol.json), [evaluator](clock_test.py) and [results](results.json) here so readers can inspect the inputs and repeat the nearest-zero check. This is a retrospective public deposit of the earlier pilot. The GitHub preregistration in PR #18 applies to the later 32-witness experiment.

| Clock input | Distance at clock | Distance at disjoint $\pi n$ control | Closer center |
|---|---:|---:|---|
| Lower transverse offset | 0.08998343 | 0.07433149 | Grid |
| Higher transverse offset | 0.02976868 | 0.06873834 | Clock |

I predicted the clock would win at both inputs. It won at one. The disjoint-grid rule put the controls about 2.83 and 13.54 local mean zero spacings from their clocks. In the second case that rule skipped the closest multiple of $\pi$. This difference motivated the symmetric controls in the larger experiment.

With Python 3.12.11, python-flint 0.9.0 and FLINT 3.6.0, copy only `clock_test.py` to an empty directory. Replace REPO below with the absolute path to the Super Zeta repository. Run from the directory containing the copy.

```text
python -B clock_test.py freeze REPO
python -B clock_test.py test 3f51d2bf0ed501d1f1dfba019f534102a22bc8e52e77009fc42b3e494ccd32ff
```

The first command recomputes the orbit checks and the two control centers. The second determines how many zeros lie below each center and encloses the immediately adjacent ordinates. The recorded results include both ordinates, their global indices, and the directed distance intervals.

A [separately written 128-bit replay](replay_128.py) began from the rational inputs, recovered the four global counts and refined the eight adjacent ordinates before reading the original answers. All sixteen intervals compared across precisions overlapped. Both evaluators use FLINT. The [128-bit record](replay_128.json) lists the enclosures and overlap checks. To repeat this replay, copy its script, the original protocol and the 96-bit results into an empty directory and run `python -B replay_128.py` there.
