# The rotations in multiples of π

I start the blue branch at the fourth Riemann zero with the native multiplier angle $\theta=\pi/3$. The clockwise turn already taken is $\alpha=\pi/3-\theta$. I give $\alpha$ as a positive distance; the signed change in angle is $-\alpha$. The three interior rows are rounded from directed enclosures. The endpoints have exact angles. [All three enclosures and crossing directions](blue-crossings.json) · [Reproduce the count](blue_crossings.py)

| Point on the blue branch | Native angle $\theta$ | Clockwise turn $\alpha$ | Degrees turned | Riemann height | Ordinary zeta magnitude |
| --- | ---: | ---: | ---: | ---: | ---: |
| Leave the fourth zero | $\pi/3$ | $0$ | 0° | 30.424876 | 0 |
| Cross to the left | $0.299235659\pi$ | $0.034097675\pi$ | 6.137581° | 33.035367 | 0.142187 |
| Upper loop crosses to the right | $0.263252491\pi$ | $0.070080843\pi$ | 12.614552° | 35.225270 | 2.920990 |
| Upper loop crosses back to the left | $0.262246950\pi$ | $0.071086383\pi$ | 12.795549° | 35.325132 | 2.938889 |
| Land at the elementary address | $\pi/4$ | $\pi/12$ | 15° | 36.258881 | 4.055336 |

The first crossing occurs about 0.100306 above the fifth zero. The entire upper loop in the pictured crossing neighborhood is below the sixth zero, whose height is about 37.586178. At a recorded point between the upper crossings the real part is 0.50053190598. A full-width plot makes the two crossings there look like a single contact. All three crossings are zeros of the moving reference, and ordinary zeta stays nonzero on the entire open arc. [Fifth and sixth zero isolation and replay](README.md) · [Bound over the open blue arc](../Dottie-Forward-Iteration/interior_2.json)

## Why the addresses also contain π

The angle of the spire sweeps by $\pi/12$ in every row below. The factor $2\pi k$ in a starting address records another angle: it is the phase in $p^{it}=\exp(it\log p)=1$, so $t=2\pi k/\log p$. The integer $k$ counts full rotations of that exponential. It is a different index from the Riemann zero's rank by height.

| Exact elementary seed | Full turns of the elementary phase | One $60^\circ$ to $45^\circ$ sweep lands at | How the connection was found |
| --- | ---: | --- | --- |
| $4\pi i/\log 3$ | $k=2$ for base 3 | First Riemann zero | Exploratory, then checked forward |
| $6\pi i/\log 3$ | $k=3$ for base 3 | Escapes left | Finite continuation and Fourier tail |
| $8\pi i/\log 3$ | $k=4$ for base 3 | $6\pi i/\log 2$ | Prespecified comparison |
| $10\pi i/\log 3$ | $k=5$ for base 3 | Fifth Riemann zero | Retrospective inverse and forward replay |
| $12\pi i/\log 3$ | $k=6$ for base 3 | Sixth Riemann zero | Retrospective inverse and forward replay |
| $4\pi i/\log 2$ | $k=2$ for base 2 | Second Riemann zero | Forward prediction |
| $8\pi i/\log 2$ | $k=4$ for base 2 | Seventh Riemann zero | Exact reset during the failed fifth-zero prediction |

[Chronology and original source records](../README.md#how-the-cases-were-selected)
