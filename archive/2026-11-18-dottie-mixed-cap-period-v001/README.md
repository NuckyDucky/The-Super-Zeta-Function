# The marked cap approaches an orbit of period 205,440 at six Dottie inputs

I found six parameters where the marked starting point $(1,1)$ approaches cycles of different lengths in its two coordinates. On the negative flank, the first coordinate has primitive scalar period 321 and the second has primitive scalar period 320. The attracting orbit has primitive period **205,440** under the original ordered map. The cap itself converges to that orbit.

**To reproduce the result**, download the [standalone Python verifier](verify_mixed_cap_period.py). It contains every input and independently checks both coordinates. In a Python 3.12 environment run

```sh
python -m pip install python-flint==0.9.0
python -B verify_mixed_cap_period.py
```

The script runs all six inputs at 1,024 and 2,048 bits and prints a signed direction interval and an upper bound for the second coordinate's return derivative at each one. The [original certificate ZIP](dottie-cap-periods-320-and-321.zip) includes the earlier two verification methods, the 14-input ledger, the full-box continuation and the frozen inputs. [Hosted verification runs](https://github.com/NuckyDucky/The-Super-Zeta-Function/actions/workflows/mixed-cap-period.yml)

### Inputs and return maps

I use the exact rational parameters from [the 32-input protocol](../2026-11-18-clock-local-controls-protocol-v001/protocol.json). Set $y=0.509892982511772$ and

```math
x_j=4.749479070945369\times10^{-8}+\frac{2j-33}{32}\,3\times10^{-10},
\qquad L=-x_j+iy,\qquad j\in\{4,6,12,13,19,28\}.
```

One application of $F_L(P,Q)=(e^{LQ},e^{-LP})$ exchanges the roles of the coordinates. Its square acts by $g_L$ on $P$ and $g_{-L}$ on $Q$, where $g_L(z)=\exp(L\exp(-Lz))$. Reflection $L\mapsto-\overline L$ conjugates the two recurrences and exchanges the coordinates. It gives the reflected six witnesses as well.

### What happens on the 321st step

Let $r=10^{-300}$. The calculation starts with an interval enclosure of the **entire** disk $|z-1|\le 2r$. At each of 319 steps it encloses both real and imaginary parts. Write $b=L\exp(-Lz_{319})$, so $z_{320}=\exp(b)$. The sign needed for the next exponential is given by the exact identity

```math
\Re(-Lz_{320})=e^{\Re b}\,d,\qquad
d=-(\Re L)\cos(\Im b)+(\Im L)\sin(\Im b).
```

For all six inputs, $\Re b>10^{177}$ and the **whole interval** for $d$ lies below $-0.0437$. The closest case is input 12, where the standalone verifier prints $-0.043707803\ \pm\ 3.89\times10^{-10}$. It takes sine and cosine on an interval containing every possible $\Im b$ from the initial disk. Thus $\Re(-Lz_{320})<-1000$. Since $|L|<1$, the full next image satisfies

```math
|g_L^{321}(z)-1|\le \exp(\exp(-1000))-1 < 5.076\times10^{-435}.
```

Cauchy's derivative estimate on radius-$r$ circles inside the doubled disk gives a return derivative below $5.076\times10^{-135}$ throughout the inner disk. The return maps that disk strictly inside itself and contracts it, so the cap $1$ converges to its unique fixed point under the return. Its step-3 and step-107 images are each more than $0.939$ from $1$. These two tests exclude each proper divisor of $321=3\cdot107$.

### Why the other coordinate has period 320

For $g_{-L}$ I use the disk of radius $0.01$ centered at $0.99959169-0.00920827i$, which contains $1$. This center is a shortened decimal from the Phase 3K continuation. The standalone script checks this disk directly for each exact parameter. For a half-step with rate $a$, center $c$ and disk radius $h$, the radius of the image about $e^{ac}$ is at most $|e^{ac}|(e^{|a|h}-1)$. I add the rounding enclosure when recentering and multiply the derivative bounds for the successive disks. After 320 scalar steps the image lies strictly inside the original disk and the derivative bound is below $0.352$ at all six inputs. The step-64 and step-160 images are disjoint from the disk. These exclude each proper divisor of $320=2^6\cdot5$ and certify capture at primitive period 320. [Dottie manuscript, finite witnesses](../2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L579-L603)

### Why the ordered period is 205,440

Under $F_L^2$ the limiting product point returns exactly when both coordinates return, first at $\operatorname{lcm}(321,320)=102720$. For a point of primitive period $m$ under $F_L$, its period under $F_L^2$ is $m/\gcd(m,2)$. The even value 102,720 forces $m=205440$.

I identified these six inputs after the zeta proximity experiment. Its published score remains 20 clock wins, 16 control wins, and 28 unresolved comparisons. The period checks use only the exponential dynamics. [Original experiment and scoring](../2026-11-18-clock-proximity-results-v001/README.md)

### Verification record

The standalone check and the original packet use directed interval arithmetic with python-flint 0.9.0. The original packet includes a separate midpoint-radius calculation and a rectangular calculation at up to 3,072 bits. Both depend on FLINT. The new verifier uses the frozen rational inputs, a shortened Q-disk center and direct enclosures of both cap returns. The hosted job replays it and both original period-321 calculations in a fresh Linux environment. Archive checksums cover every file. The original ZIP has SHA-256 `4cb6a7c28be7845ee78eb301b510894b4c60b9f87c4b8118dfaf0f0f2982f4ca`.
