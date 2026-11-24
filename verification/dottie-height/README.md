# From the marked Dottie return to the measuring disk

I keep the two phases of the tetrational lift, with the cap at `(1,1)`. If each scalar phase has primitive period $320$, Lean gives primitive period $640$ for the original ordered map. The lifted derivative of the arrow with rate $r$ is $r$. If one marked arrow occurs $p$ times, its change in log scale from the midpoint to the flank is

$$
d=p\log\frac{|x+iy|}{y}=\frac p2\log(1+(x/y)^2).
$$

The return winding supplies $|k|$. The selected height satisfies $Td=2\pi|k|$. With $p=320$ and $|k|=1$, the positive inverse is $x=y\sqrt{\exp(2\pi/(160T))-1}$. If $|T-T_D|\le10^8$, Lean puts this unique $x$ inside the archived flank interval of half-width $10^{-12}$. If the real part lies in the measuring range, the same input $w$ lies in the disk for $T=\Im w+1/512$. [Inverse and endpoints](../../lean-ideal73/DottieHeightTransport.lean) · [Clock, winding and disk](../../lean-ideal73/DottieMarkedHeight.lean)

The 384-bit Arb replay checks cap capture, contraction, the exclusions at periods $64$ and $160$, and the principal argument strip on each entire flank interval. It keeps $P,Q$ separate on both flanks. The two windings on the left are $+1$, and the two on the right are $-1$. The Lean marked-return theorem takes those orbit properties as hypotheses. [Replay source](../../tools/dottie-compute-pilot/replay_dottie_height_band.py) · [Replay result](flank-replay.json)

## The signed bounds

- `hscore` checks the archived score for the normalization. It supplies the positive reference lower bound used by the retained and far-tail estimates. [Reference theorem](../../lean-ideal73/DottieReferenceQuantitative.lean)
- `hsharp` and `href` are the moment checks for the retained contribution in this normalization. `hsigned` is the upper bound on the imaginary part of the shorter omitted sum, on the same circle. [Moment checks](../../lean-ideal73/DottieMomentArchiveScores.lean) · [Shorter omitted sum](../../lean-ideal73/DottieShorterOmittedBudget.lean)
- If the retained imaginary part is at most $-A$ and the omitted imaginary part is at most $B$, the contradiction needs $B<A$ at the recovered input. The quartic uses $A=190(\Re w-1/2)S_0$ and $B=189(\Re w-1/2)S_0$. The field theorem keeps the same-input zero implication, reflection and coverage as explicit hypotheses. [Strict-gap theorem](../../lean-ideal73/DedekindDottieSetup.lean)
- Lee Crossley’s compact difference has $K(X)=2D(X/2)-D(X)$, where $D(X)=R(X)-R(X/2)$ is a signed shell. If I have an upper bound for the first shell and lower bounds on $K$ along the dyadic scales, Lean gives an upper bound for the later shells. For the Dottie estimate, $R$ can be the weighted signed prefix at a fixed $w$. [Lee’s filter](https://github.com/NuckyDucky/The-Super-Zeta-Function/pull/50) · [Shell recovery](../../lean-ideal73/CrossleySignedTail.lean)
- `hR` and `hB` eliminate the ordinary and beta factors at the original input. The Lean adapter accepts Mathlib’s `RiemannHypothesis` for `hR`. Lee’s pinned `ordinary_rh` has this exact type. For the general field, the factorization or zero identity determines the analogous inputs. [Ordinary RH declaration and replay](https://github.com/leecrossley/crossley-criteria-riemann-hypothesis/tree/5fdcf17aef81eed22eded82acc29519ae4ff92c7/theta-window)

## Replay

With the pinned mathlib cache populated, run `lake build DottieHeightVerification` from `lean-ideal73`. The target prints the theorem statements and checks the transitive axioms. [Lean audit](../../lean-ideal73/DottieHeightVerification.lean) · [Build and axiom output](lean-build-and-axioms.txt)

From the repository root, the independent interval replay uses Python 3.12 and python-flint 0.9.0.

```sh
python -m pip install python-flint==0.9.0
python -B tools/dottie-compute-pilot/replay_dottie_height_band.py
```
