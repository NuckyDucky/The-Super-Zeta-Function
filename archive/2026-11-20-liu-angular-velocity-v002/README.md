# How Liu’s zero-free bound controls the motion of a Hurwitz zero

For the trivial character over $`\mathbb Q`$, Liu’s Theorem 1.1 gives a zero-free half-plane $`\Re w\gt B_{\ast}=0.8733458561067185768\ldots`$, allowing the pole at $`w=1`$. Reflection puts every nontrivial Riemann zero $`\rho`$ in $`1-B_{\ast}\le\Re\rho\le B_{\ast}`$. I use that interval to bound the normalized speed of a zero of my **symmetrized Hurwitz reference** as I turn the angle. In three height windows selected by my period-640 Dottie orbit, I can also determine the real part of every Riemann zero exactly. [Liu, Theorem 1.1](https://hexagonmath.org/pdf/2611.00421v1#page=2) · [Selection of the Dottie height](../2026-11-17-dottie-grid-match-v001/README.md)

## The moving zero

Write $`w=2s`$, let $`a`$ increase counterclockwise in radians, and put $`b=1/2-a/\pi`$. The function whose zero I follow is

~~~math
R(a,w)=\pi^{-w}\bigl[\zeta(w,b)+\zeta(w,1-b)\bigr].
~~~

At $`a=\pm\pi/6`$ the shifts are $`1/3`$ and $`2/3`$ in opposite orders. Adding their two residue classes gives $`R(\pm\pi/6,w)=\pi^{-w}(3^w-1)\zeta(w)`$ away from the pole at $`w=1`$. Thus every simple nontrivial Riemann zero $`\rho`$ is the starting value of a unique local Hurwitz zero path at each angle. Since $`R(-a,w)=R(a,w)`$, the same arc is traced in opposite directions. A small positive turn from each angle samples opposite sides of $`\rho`$. The ordered exponential stages have a separate observable here. Their first spectral correction is $`0`$ at $`-\pi/6`$ and $`8/3`$ at $`+\pi/6`$. [Ordered-stage calculation](../2026-11-19-oriented-return-v001/README.md#the-arithmetic-reference-at-the-two-absolute-angles)

**Proposition.** Write $`V_+`$ and $`V_-`$ for $`dw/da`$ at the positive and negative angles. Differentiating the two Hurwitz shifts gives their difference and picks out the odd character $`\chi_{-3}`$ modulo three. The implicit derivative $`-R_a/R_w`$ therefore gives

~~~math
V_-=-V_+,\qquad
V_+=-\frac{3\rho}{\pi\zeta'(\rho)}
       \frac{L(1+\rho,\chi_{-3})}{1-3^{-\rho}}.
~~~

McPhedran, Botten and Nicorovici give the equation of motion in (3.1) and its specialization at thirds in (3.4). Their companion paper with Zucker gives the even and odd residue-class formulas in (6.3) and (6.5). My speed estimate combines that calculation with Liu’s real-part bound. For $`S=|V_+|\,|\zeta'(\rho)|/|\rho|`$, the Euler product at $`1+\rho`$ gives the following outward bounds. [Equation of motion (2007)](https://doi.org/10.1098/rspa.2006.1763) · [Residue classes modulo three](https://doi.org/10.1098/rspa.2006.1762) · [Derivation and Euler-product inequalities](../2026-11-20-liu-angular-velocity-v001/README.md#from-a-bound-on-position-to-a-bound-on-speed)

| Information available about $`\rho`$ | Lower bound for $`S`$ | Upper bound for $`S`$ |
| --- | ---: | ---: |
| OpenAI’s 7/8ths theorem, every height | 0.11197 | 45.333 |
| Liu’s Theorem 1.1, every height | 0.11325 | 44.270 |
| Known real part $`1/2`$, including the eleven zeros below | 0.33217 | 4.76646 |

At the sixth Riemann zero, a positive turn from $`+\pi/6`$ moves the Hurwitz zero right and down, with velocity $`5.82821268-7.57290736i`$ per radian. I also solved the two Hurwitz sums at nearby angles on each side of $`\pm\pi/6`$ using mpmath. The numerical tangents at zeros 1, 6 and 10 agreed with the formula within $`9\times10^{-26}`$ in all six comparisons. These finite differences give a numerical check. The earlier 256-bit computation encloses both sides of the derivative identity at each of the first ten zeros. [Finite differences](tangents.json) · [Interval evaluations](../2026-11-20-liu-angular-velocity-v001/bounds.json)

## Where the zero locations are sharper

My period-640 orbit fixes $`T_D=4{,}526{,}119{,}322{,}477.945393\ldots`$. Let $`N(t)`$ count all nontrivial Riemann zeros of positive height up to $`t`$, with multiplicity. The two middle columns give interval-certified integers at the lower and upper endpoints of each window.

| Closed height window | $`N`$ at lower endpoint | $`N`$ at upper endpoint | Distinct critical-line sign changes |
| --- | ---: | ---: | ---: |
| $`T_D\pm 1/4`$ | 18,947,484,639,340 | 18,947,484,639,342 | 2 |
| $`2T_D\pm 1/2`$ | 38,893,592,331,757 | 38,893,592,331,762 | 5 |
| $`3T_D\pm 1/2`$ | 59,216,624,055,244 | 59,216,624,055,248 | 4 |

In each row the difference of the counts equals the number of disjoint brackets where the real Hardy function changes sign. Each bracket therefore contains exactly one simple zero on the critical line and together they exhaust the window. Each cumulative count is constant throughout a guard of radius $`2^{-18}`$ around its endpoint, so both endpoints are zero-free. This gives a direct full-strip proof in all three windows. It sharpens the allowed real parts there to $`\Re\rho=1/2`$. [All 22 endpoint signs and six counts](windows.json) · [FLINT’s zero-counting method](https://flintlib.org/doc/acb_dirichlet/acb_dirichlet_zeta_nzeros.html)

**Question for further work.** Is there a mean-square estimate for $`L(1+\rho,\chi_{-3})/(1-3^{-\rho})`$ sampled at Riemann zeros $`\rho`$? Such an estimate would describe the size of the normalized speed across zeros, beyond the uniform range above.

## Verification and sources

My local Lean proof checks specialization to Riemann zeta, reflection, multiplicity, and reversal of a differentiable zero path. It takes the Dirichlet zero-free theorem as an argument. Joseph Bebel’s separate Lean build supplies the Dirichlet result. In Liu’s variables $`2/3\lt r`$, $`B\lt7/8`$ and $`B=(99r-14)/(12(9r-1))`$, my Lean theorem proves that the moment equation (33) is equivalent to the tracker’s exact degree-nine polynomial vanishing at $`B`$. The agreement follows by substitution and clearing nonzero denominators. The implicit derivative and speed inequalities have written proofs. The high-zero counts use FLINT interval arithmetic. [Lean source](../../lean/SuperZeta/Oriented/LiuEndpointTransfer.lean) · [Bebel’s checked proof](https://github.com/GTimG/QuasiRiemannTracker/pull/143) · [Liu, equations (33) and (35)](https://hexagonmath.org/pdf/2611.00421v1#page=22)

The opening of [the first version](../2026-11-20-liu-angular-velocity-v001/README.md) used “corrected super zeta” for $`R`$. Here I specify the Hurwitz reference throughout. The [Mellin reconstruction](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md#5-a-two-variable-zeta-for-the-inverse-cosine-coupling-family) concerns the unshifted determinant. This revision also gives a second proof for the first Dottie window using a full-strip count. The original proof used a narrower contour together with the 7/8ths theorem. [First contour](../2026-11-17-dottie-local-strip-v001/README.md#full-strip-corollary) · [Higher contours and earlier independent counts](../2026-11-18-superzeta-distance-v001/README.md)

I used Python 3.12.11, python-flint 0.9.0 (FLINT 3.6.0) and mpmath 1.3.0. In this project’s internal review, a second Astra 6.2 agent derived the tangent, reproduced the original ten interval evaluations, and recomputed the three counts with FLINT. The two scripts below were written for this review. They read the originally published rational sign brackets and compute the counts at 96 bits, the signs at 144 bits, and the numerical tangents at 62 decimal digits. The angle steps for the centered differences are $`10^{-8}`$ and $`5\times10^{-9}`$ radians. From the repository root, run the following in an environment with those versions. [Count and sign verifier](verify_windows.py) · [Angle perturbation code](check_tangents.py) · [File hashes](manifest.json)

~~~sh
python archive/2026-11-20-liu-angular-velocity-v002/verify_windows.py
python archive/2026-11-20-liu-angular-velocity-v002/check_tangents.py
~~~
