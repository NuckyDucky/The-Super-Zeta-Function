# Where does a zero move as the recursion deepens?

At two finite orders of the quartet reconstruction, a single Newton step predicted the angle of a moving zero to within $0.001^\circ$. A separate experiment at height $9.052\times10^{12}$ tested whether zeros repeat after the Dottie clock completes another turn. The higher window contained three simple Riemann zeros on the critical line. Neither of the two inherited height intervals contained a zero. The finite-layer calculation measures how an approximation changes with depth. The high-window calculation counts zeros of the completed response.

## A direction from the next layer

Write $w=\beta+iT=2s$. For a local height origin $T_0$, let $X=\beta-1/2$ and $Y=T-T_0$. Positive angles turn counterclockwise from the positive $X$ axis. Dividing by two to obtain $s$ preserves the bearing.

The original quartet construction uses $\alpha_{n,\sigma,\tau}=\exp(\sigma t_n+i\tau\theta_n)$. Its marked factors contain $\exp[(w-1/2)(\sigma t_n+i\tau\theta_n)/2]$. For a displacement $d=\Delta X+i\Delta Y$, the change of the outer-to-inner ratio at fixed conjugate label is $R=\exp(t_nd)$. The change of the positive-to-negative conjugate-label ratio at fixed radial label is $Q=\exp(i\theta_nd)$. Taking moduli recovers both displacements exactly:

$$
\Delta X=\frac{\log|R|}{t_n},\qquad
\Delta Y=-\frac{\log|Q|}{\theta_n}.
$$

To **predict** motion, we used the unprefactored partial Mellin sum $A_K$ defined by the [coupling recurrence](../2026-11-17-quartet-return-recursion-v001/quartet-return-phase.tex). Set $h(v)=v\,\mathrm{sech}^2\sqrt{v}$ and $r(v)=h(v)/(1+h(v))$. Summing the geometric series gives

$$
A_K(w)=\int_0^\infty v^{-w/2-1} h(v)(1-r(v)^K)\,dv.
$$

At the old zero $\rho_K$, linearization of $A_{K+1}$ gives the proposed displacement $d=-A_{K+1}(\rho_K)/A'_{K+1}(\rho_K)$. The predictor fixed $d$ before separately locating the next zero. The searches used given Riemann ordinates as initial seeds. Evaluation of the finite layers used the integral above.

| Depth | Height near | Predicted bearing | Measured bearing | Distance from predicted endpoint to next zero |
|---|---:|---:|---:|---:|
| 40 to 41 | 32.935 | $-119.307487^\circ$ | $-119.308279^\circ$ | $9.24\times10^{-10}$ |
| 60 to 61 | 48.005 | $124.685823^\circ$ | $124.685914^\circ$ | $1.06\times10^{-12}$ |

**Directed certificates.** At 384 bits, interval integration and analytic tails enclosed each integral and its derivatives. On each circle of radius $10^{-43}$ about a refined numerical center $c$, the check verified $|A_K(c)|+20r^2<|A'_K(c)|r$, using $|A_K''|<40$ throughout the disk. Rouché's theorem gives one simple finite-layer zero in each of the four disks. The bearing calculation also propagates the uncertainty in the old zero. The printed centers have fewer digits than the internal disk centers. [Calculation](native_zero_angle_step.py) · [Directed bearings and endpoint differences](native-angle-results.txt)

At fixed depth $K=60$, the horizontal displacement $\beta-1/2$ near height 32.935 was approximately $1.47244\times10^{-15}$. Near height 48.005 it was $5.90158\times10^{-7}$, about $4.01\times10^8$ times larger. At the higher ordinate the displacement fell to $2.85559\times10^{-8}$ by depth 63. These give two height samples and one finite sequence of refinements. The deeper ratios in the replay output are numerical quadrature comparisons; lines explicitly marked “CERTIFIED” report the disk checks. [Finite-layer calculations](track_native_superzeta_layers.py) · [Layer results](layers-results.txt)

## The second Dottie harmonic

The [frozen first-harmonic selection](../2026-11-17-dottie-grid-match-v001/README.md) gives $T_D=2\pi/[160\log(1+(x/y)^2)]$ from the two marked finite-orbit witnesses with $x=4.749479070945369\times10^{-8}$ and $y=0.509892982511772$. This test translates each first-harmonic zero's certified height interval upward by exactly $T_D$. The frozen boxes retain their original widths in height and cover $1/16<\beta<15/16$.

At the new center $2T_D=9052238644955.8907866384146577\ldots$, the 192-bit count in $|T-2T_D|<1/4$ was **three**. The heights relative to the new center are approximately $-0.23817429$, $-0.02427886$, and $+0.08022380$. Each lies in its own critical-line sign bracket. Total winding and the three sign brackets account for all multiplicities inside the rectangle. The [preceding full-strip argument](../2026-11-17-dottie-local-strip-v001/README.md) applies at this height using the cited global seven-eighths theorem and reflection.

Both frozen translated boxes had winding count zero. The new upper line zero lies about $0.00186557$ below the translated upper bracket midpoint. [Frozen prediction](dottie-second-harmonic-plan.json) · [Contour counts and rational brackets](dottie-second-harmonic-count.json) · [Replay of the count](contour-results.txt)

For the two-dimensional calibration the chosen probe was $X=1/512$ at the translated upper midpoint. At 320 bits, the first Newton correction of the completed Riemann function $\xi$ predicted $-135.630286^\circ$. The independent zero bracket gives $-136.3134^\circ$ (enclosure radius below $0.000061^\circ$). Three steps reached the certified height bracket. The first step uses the completed-function logarithmic derivative, including the digamma term, and a Cauchy bound on the error in the symmetric difference for $\zeta'$. The target bracket enters only during comparison. [Local computation](dottie_local_angle.py) · [Angle and step enclosures](high-angle-results.txt)

## Factorial phase between neighboring quartet levels

With $B_n={2n\choose n}/4^n$, $D_n=\pi n B_n^2$ and $C_n=[R_n/(2\pi n)]D_n$, direct division gives

$$
\frac{D_{n+1}}{D_n}=1+\frac{1}{4n(n+1)}.
$$

The magnitude of the unwrapped adjacent factorial phase difference from the factor $D_n^{-w/2}$ is therefore $(T/2)\log(1+1/[4n(n+1)])$ at positive height $T$. At $T_D$, its half-turn straddles levels 424,367 and 424,368. Substituting the actual $C_n$ into the same phase calculation yields opposite signs of the excess over $\pi$ at levels 424,329 and 424,330. The two sign brackets are 38 levels apart. The corrected calculation establishes a local bracket. [Factorial derivation and Stirling control](../2026-11-16-super-zeta-v001/research/binomial-normalization.md) · [Directed phase calculation](dottie_factorial_phase.py) · [Endpoint enclosures](factorial-results.txt)

## Reproduce

Use Python 3.12 and the full repository checkout so the earlier snapshot inputs are present. From this snapshot directory run the following commands. The optional argument selects one calculation. Omitting it runs all five. Each calculation stages its inputs in a new temporary directory.

~~~sh
python -m pip install -r requirements.txt
python -B replay.py native-angle
python -B replay.py high-angle
python -B replay.py layers
python -B replay.py factorial
python -B replay.py contour
~~~

The contour replay regenerates the plan before evaluating zeta and compares the complete regenerated JSON records with their archived counterparts. The other modes print results for comparison with the corresponding text logs. Use Python assertions in the replay. The [provenance record](provenance.json) lists original source hashes and the tested environment.
