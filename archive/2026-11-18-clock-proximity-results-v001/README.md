# Can the Dottie return select heights closer to Riemann zeros?

I tested the Dottie clock against two nearby controls at each of 32 transverse inputs. **The clock won 20 comparisons, the controls won 16, and 28 comparisons remained unresolved.** The 18 inputs that passed the orbit check favored the clock by four comparisons. The preregistered prediction required a majority across all 64 comparisons. The data leave that majority undecided.

| Within one input | Number of inputs |
|---|---:|
| Clock closer than both controls | 7 |
| Clock closer than one control | 6 |
| Both controls closer than the clock | 5 |
| Orbit check unresolved | 14 |

[All 32 rows with heights, distances and votes](comparisons.csv) · [Frozen protocol](../2026-11-18-clock-local-controls-protocol-v001/protocol.json) · [Directed zero enclosures](results.json) · [Orbit records and reasons for unresolved rows](orbits.json)

## What the score measures

I prescribed 96 windows between about $4.47\times10^{12}$ and $4.59\times10^{12}$ in Riemann height. Each clock height had a control four local mean zero spacings below it and another four above it. At each of the 54 eligible centers, FLINT computed the global count $N(H)$ and enclosed the zeros with consecutive indices $N(H)$ and $N(H)+1$. All 54 nearest distances were strictly below the cap of one quarter, and all 36 comparisons resolved at 96 bits. This experiment measures proximity in height. The earlier [full contour counts](../2026-11-18-superzeta-distance-v001/README.md) address the real parts and multiplicities in three particular windows. [FLINT zero-isolation method](https://flintlib.org/doc/algorithms/special-functions/zeta-zeros.html)

For 18 inputs I certified the primitive scalar period 320 and unit absolute winding of each marked return at the midpoint and both flanks. All 14 other inputs passed the midpoint check. At their first flank, propagation of the cap enclosure exceeded the allowed trapping radius of $10^{-27}$ on each attempt, including the final one at 1,536 bits and 144 laps. The check stopped before deciding capture or winding there. Under the published rule these inputs get two unresolved votes apiece. They retain their places in the denominator. Reflection supplies the other quartet addresses at the same nominated height.

The lowest possible score is $20/64=31.25\%$ and the highest is $48/64=75\%$. These are the exact limits from the missing comparisons. Each clock participates twice. The experiment uses one horizontal slice and supplies no independence model for a significance test.

## Why the transverse input matters

On the positive flank at fixed $y$, the one-winding clock can be inverted exactly:

```math
H=\frac{\pi}{80\log(1+(x/y)^2)},\qquad
x=y\sqrt{\exp\!\left(\frac{\pi}{80H}\right)-1}.
```

At the original witness the local mean spacing in Riemann height is about $0.230128$. Substituting $H$ and $H+0.230128$ in the inverse changes $x$ by about $1.21\times10^{-21}$. Whenever an interval of inputs shares the same period, the clock formula assigns a continuous range of heights across it. A zero-proximity prediction therefore depends on which transverse input is selected within the slice. Here that choice was fixed by the 32 equally spaced midpoints before evaluating any zeros.

## Chronology and reproduction

GitHub recorded [PR #18](https://github.com/NuckyDucky/The-Super-Zeta-Function/pull/18) at 03:24:12 UTC on November 19, 2026. The [first commit](https://github.com/NuckyDucky/The-Super-Zeta-Function/commit/cfc5e78314f6d82f23307f29118f7ddfec8fea5c) held the inputs, evaluator, controls, eligibility rules, budget and score before the new zero evaluations. The protocol SHA-256 is `26007a2e0f65a12abd39485347976dfb28c018c4736a659500d0d7fa0672183f`. Results were computed with Python 3.12.11, python-flint 0.9.0 and FLINT 3.6.0. The [protocol README](../2026-11-18-clock-local-controls-protocol-v001/README.md) gives the full replay commands.

To check the score directly from the archived brackets, run `python -B check_records.py` with assertions enabled. It verifies the input hashes, the two signed comparisons for every eligible row, the unresolved rows, and the attainable score interval. The orbit routines at the pinned upstream commit are `verify_dottie_horn_slice.py` (SHA-256 `4b801849c9d531683368b5499de097b1325556dc4c3f7bef114c989863e2a2b2`) and `dottie_multiplier_winding.py` (`aaa9fe379c183a2b56c23b2a0e1c1ecf7af185713c305e4e4c12e76f6f7d8d01`).

The [earlier two-height pilot and its 128-bit replay](pilot/README.md) are preserved here for comparison. That pilot used the nearest disjoint multiple of $\pi$ as its control. The grid won the first comparison and the clock won the second.
