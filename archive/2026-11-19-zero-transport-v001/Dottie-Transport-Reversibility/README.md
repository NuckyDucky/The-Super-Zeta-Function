# Reversing a regular turn

[Rotation table and three critical-line crossings](rotations.md) · [Exact base-three start-only theorem](TriadicStart.lean) · [Lean replay record](triadic_lean_check.json)

I asked whether two distinct seeds can merge when the same angular turn carries each one along a continuous path of simple zeros. The answer is no. Reversing the angle recovers the source on every such path. This applies to a single sweep before any reset.

Let the shift run from $a=1/6$ to $b=1/4$ and write the comparison family as

$$
R(t,w)=\pi^{-w}\bigl[\zeta(w,t)+\zeta(w,1-t)\bigr].
$$

Call a path regular on this interval if it is continuous and finite at every point of the closed interval, avoids the pole at $w=1$, and satisfies $R(t,w(t))=0$ and $\partial_wR(t,w(t))\ne0$ throughout. Both endpoints are included. A continuous finite path on this compact interval has compact image. Local analytic continuation in the shift is available along it because $t,1-t>0$.

**Proposition.** Transport from $a$ to $b$ is one-to-one on the set of seeds admitting a regular path on the whole interval. Transport from $b$ back to $a$ is its inverse on the set of reached endpoints.

**Proof.** For two regular paths, the set of shifts where their values agree is closed by continuity. At a common value the local implicit-function theorem supplies a unique nearby zero as a function of the shift, since the derivative in $w$ is nonzero. Continuity puts both paths in that same neighborhood, so the equality set is also relatively open. The interval is connected. If the paths agree anywhere, they agree throughout. Agreement at $a$ gives a unique forward branch and agreement at $b$ a unique source. Reversing the parameter direction gives a regular path back over the same interval.

The proof is local to the chosen continuous paths. It leaves open which endpoints admit such a path across the entire sweep. It also leaves open the order of their imaginary parts. The previous forward experiment reached ordinary zero number 7 from the elementary address $8\pi i/\log 2$.

**Numerical round trip.** I started from the certified box for ordinary zero number 7. At 288 bits, 621 overlapping contracting disks tracked it from $45^\circ$ back to $60^\circ$. The resulting imaginary coordinate was $36.2588811346175505$, enclosed within $3.30\times10^{-17}$ of that decimal. The solver used the terminal box from the forward identification and generated a fresh descending mesh using 192 base cells. It read no earlier trajectory samples or source address during the continuation. After sealing the result, I tested the two elementary lattices at $60^\circ$. The isolation disk contained the exact point $8\pi i/\log 2$, identifying the returned seed.

[Full reverse record](reverse-path.json) · [Exact endpoint identification](reverse-identification.json) · [Reproduction script](reverse.py)

Run `python -B reverse.py` with Python 3.12 and python-flint 0.9.0. Place `Dottie-Forward-Iteration` and `Dottie-Off-Axis-Return` beside this directory. The input is the archived `identification_3.json`. The regular-branch proposition is proved above by the implicit-function theorem. The numerical check uses FLINT directed ball arithmetic.

### Why the single chain misses zeros 5 and 6

In a retrospective experiment I isolated each skipped zero inside its own interval. The cumulative number of Riemann zeros rises from 4 to 5 between the fourth zero and the intermediate elementary height, and from 5 to 6 between that height and the seventh zero. I bisected a sign change of Hardy's $Z$ in each interval 112 times, then followed each isolated zero backwards. The locations recovered and replayed were

| Ordinary zero at the end | Height, rounded | Sole regular predecessor | Certified tubes, backwards / forwards |
| --- | ---: | --- | ---: |
| $\rho_5$ | 32.93506158773919 | $10\pi i/\log 3$ | 461 / 461 |
| $\rho_6$ | 37.58617815882567 | $12\pi i/\log 3$ | 1,397 / 1,397 |

I sealed each reverse endpoint before testing it against the two elementary lattices at $60^\circ$. I then ran a fresh clockwise continuation from its exact lattice expression. In each case a common isolating disk at $45^\circ$ identified the returned root with the original Hardy bracket. This experiment used the two missed ordinals as inputs. It did not alter the outcomes of the earlier forward predictions.

**Corollary.** None of the nonzero starting addresses $2\pi i k/\log 3$ can be produced by a finite endpoint reset. The $45^\circ$ endpoint partition consists of the ordinary Riemann zeros and the addresses $2\pi i j/\log 2$. Ordinary zeta has no zero on the imaginary axis. For the two lattice addresses to agree we would need $k\log 2=j\log 3$, hence $2^{|k|}=3^{|j|}$ for nonzero integers of the same sign. Unique prime factorization excludes this equality.

In particular the two specific predecessors in the table occur only on the starting side of the sweep. By injectivity on regular paths they are the only regular seeds that reach $\rho_5$ and $\rho_6$, respectively. An iteration that launches elsewhere, including the run from $\rho_3$, therefore cannot acquire either skipped zero at a later finite landing while it continues by regular sweeps and exact resets.

Run `python -B missing.py 5` and `python -B missing.py 6`. [Fifth-zero source](rho5-identification.json) · [Fifth-zero return](rho5-roundtrip.json) · [Sixth-zero source](rho6-identification.json) · [Sixth-zero return](rho6-roundtrip.json)
