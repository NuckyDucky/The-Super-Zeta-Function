# Does the Dottie clock select a height closer to a Riemann zero?

I fixed 32 transverse inputs in the period-320 witness box and two nearby comparison heights for each input. My prediction is that the Dottie clock wins more than half of the 64 comparisons. Each witness supplies both a left and a right comparison, so the two scores share the same clock height.

[The protocol](protocol.json) lists every input, the three height enclosures for each input, the computation budget and the scoring rules. Its SHA-256 is `26007a2e0f65a12abd39485347976dfb28c018c4736a659500d0d7fa0672183f`. I deposited this protocol and its [evaluator](local_controls.py) before computing Riemann zeros for these windows.

For the magnitude $x$ of the transverse displacement and fixed imaginary part $y$, the one-winding clock gives

$$
H(x)=\frac{2\pi}{160\log(1+(x/y)^2)}.
$$

I use all 32 equally spaced midpoints of the published interval. At each input I test capture, primitive period and tangent winding with the [archived orbit routines](../2026-11-17-quartet-return-recursion-v001/computations). The same input determines two controls, four local mean spacings below and above the clock. The distance scored at each height is the distance to the nearest zero ordinate, capped at one quarter. A smaller clock distance earns one point and an exact tie earns half a point. Every unresolved comparison stays in the denominator with a possible score from zero to one.

## Replay

Clone the repository. In an empty working directory copy `local_controls.py` from this snapshot. With Python 3.12 and python-flint 0.9.0 (FLINT 3.6.0), run the following commands in order, replacing REPO with the absolute path to the clone. The protocol records the upstream revision and evaluator digest.

```text
python -B local_controls.py freeze
python -B local_controls.py orbits REPO 26007a2e0f65a12abd39485347976dfb28c018c4736a659500d0d7fa0672183f
python -B local_controls.py zeros 26007a2e0f65a12abd39485347976dfb28c018c4736a659500d0d7fa0672183f
```

The first command writes the frozen protocol. The second writes the orbit evidence. The third calls FLINT's zero count and consecutive indexed-zero routines and writes the component distances, votes and score. These are finite computations of proximity at the specified heights. [FLINT zero indexing](https://flintlib.org/doc/acb_dirichlet.html)
