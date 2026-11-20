# Liu’s zero-free bound and the angular velocity of a Hurwitz zero

At the two angles $`a=\pm\pi/6`$, my corrected super zeta passes through the same simple Riemann zero. Increasing both angles sends the two Hurwitz zeros in opposite directions. I use Liu’s Theorem 1.1 to bound their common speed after scaling by the local slope of Riemann zeta. The bound holds at every height. The eleven zeros in my three Dottie windows satisfy a tighter estimate because their real parts are known exactly. [Liu, Theorem 1.1](https://hexagonmath.org/pdf/2611.00421v1#page=2) · [My first window](../2026-11-17-dottie-local-strip-v001/README.md#full-strip-corollary) · [My second and third windows](../2026-11-18-superzeta-distance-v001/README.md)

## Velocity at the two angles

I use the Riemann coordinate $`w=2s`$ and measure the absolute angle $`a`$ in radians, increasing counterclockwise. Put $`b=1/2-a/\pi`$ and write the corrected reference as

~~~math
R(a,w)=\pi^{-w}\bigl[\zeta(w,b)+\zeta(w,1-b)\bigr].
~~~

Here $`\zeta(w,b)`$ is Hurwitz zeta. At $`a=\pi/6`$ the shifts are $`1/3`$ and $`2/3`$, and at $`a=-\pi/6`$ they exchange places. Gathering the two nonzero residue classes modulo three and continuing away from $`w=1`$ gives $`R(\pm\pi/6,w)=\pi^{-w}(3^w-1)\zeta(w)`$. Its prefactor is nonzero for $`\Re w\gt 0`$. The ordered dynamical traces at those angles retain their own first corrections, $`0`$ at the negative angle and $`8/3`$ at the positive angle. [Reference identity in Lean](../../lean/SuperZeta/Oriented/LiuConnection.lean) · [Derivation from my two marked exponential stages](../2026-11-19-oriented-return-v001/README.md#the-arithmetic-reference-at-the-two-absolute-angles)

**Proposition.** Let $`\rho`$ be any simple nontrivial Riemann zero. At each of the two angles there is a unique local zero path through $`\rho`$. Let $`V_+`$ and $`V_-`$ be their complex derivatives $`dw/da`$, in that order at $`+\pi/6`$ and $`-\pi/6`$. With $`\chi_{-3}`$ equal to $`1,-1,0`$ on $`1,2,0`$ modulo three, respectively,

~~~math
V_-=-V_+,\qquad
V_+=-\frac{3\rho}{\pi\zeta'(\rho)}
       \frac{L(1+\rho,\chi_{-3})}{1-3^{-\rho}}.
~~~

**Proof.** At either angle, $`R_w(a,\rho)=\pi^{-\rho}(3^\rho-1)\zeta'(\rho)\ne0`$. The shifts stay positive near the real angles and the Hurwitz sum is analytic there in both variables. The implicit function theorem gives the local path and $`V=-R_a/R_w`$. This is the equation of motion for the symmetrized Hurwitz family studied by McPhedran, Botten and Nicorovici. The identity $`R(-a,w)=R(a,w)`$ reflects one local path to the other. [McPhedran, Botten and Nicorovici (2007), §3](https://doi.org/10.1098/rspa.2006.1763) · [Hurwitz zeta and its analytic properties](https://dlmf.nist.gov/25.11.i)

Differentiating in $`a`$ gives opposite signs for the two summands. At $`a=\pi/6`$ their difference picks out the odd character modulo three,

~~~math
R_a(\pi/6,\rho)=\frac{\rho\,\pi^{-\rho}}{\pi}
\bigl[\zeta(1+\rho,1/3)-\zeta(1+\rho,2/3)\bigr]
=\frac{\rho\,\pi^{-\rho}}{\pi}\,3^{1+\rho}L(1+\rho,\chi_{-3}).
~~~

The derivative formula follows by substitution. Both velocities are nonzero since $`\Re(1+\rho)\gt 1`$, where the Euler product for the Dirichlet $`L`$-function converges absolutely. [Hurwitz shift derivative, DLMF 25.11.17](https://dlmf.nist.gov/25.11.E17) · [Dirichlet Euler product, DLMF 25.15.2](https://dlmf.nist.gov/25.15.E2)

## From a bound on position to a bound on speed

I measure $`S=\lvert V_+\rvert\,\lvert\zeta'(\rho)\rvert/\lvert\rho\rvert`$. This removes the explicit factor $`\rho/\zeta'(\rho)`$ from the velocity and lets me compare zeros at different heights. Write $`b_0\gt 0`$ for a lower bound on $`\Re\rho`$, and put $`\sigma=1+b_0`$. For each prime $`p\ne3`$, the modulus of its Euler factor lies between $`(1+p^{-\sigma})^{-1}`$ and $`(1-p^{-\sigma})^{-1}`$. Multiplying gives a lower bound $`(1+3^{-\sigma})\zeta(2\sigma)/\zeta(\sigma)`$ and an upper bound $`(1-3^{-\sigma})\zeta(\sigma)`$ for the numerator $`\lvert L(1+\rho,\chi_{-3})\rvert`$. The denominator $`\lvert1-3^{-\rho}\rvert`$ lies between $`1-3^{-b_0}`$ and $`1+3^{-b_0}`$. Thus

~~~math
\frac{3(1+3^{-\sigma})\zeta(2\sigma)}
     {\pi(1+3^{-b_0})\zeta(\sigma)}
\;\le S\le\;
\frac{3(1-3^{-\sigma})\zeta(\sigma)}
     {\pi(1-3^{-b_0})}.
~~~

Liu’s joint moment and zero-detection estimates give $`\Re\rho\le B_{\ast}`$, with $`B_{\ast}=0.8733458561067185768\ldots`$. Riemann reflection gives $`\Re\rho\ge1-B_{\ast}`$. I round this lower bound down before evaluating the formula. On the critical line I can instead put $`b_0=1/2`$. The following are outward bounds on normalized speed. [Liu, Theorems 1.1 and 7.2](https://hexagonmath.org/pdf/2611.00421v1) · [Riemann functional equation](https://dlmf.nist.gov/25.4) · [256-bit enclosures](bounds.json)

| Information about the simple zero | Lower bound for $`S`$ | Upper bound for $`S`$ |
| --- | ---: | ---: |
| OpenAI’s 7/8ths theorem, all heights | 0.11197 | 45.333 |
| Liu’s endpoint, all heights | 0.11325 | 44.270 |
| A zero on the critical line, including all eleven in my three windows | 0.33217 | 4.76646 |

For the sixth Riemann zero, near $`1/2+37.58617816i`$, I obtain $`V_+\approx5.82821-7.57291i`$ per radian and $`S\approx0.49229847`$. A small positive turn from $`+\pi/6`$ carries the moving zero right and down. The same positive turn from $`-\pi/6`$ carries it left and up. [Both angular derivatives for the first ten zeros](bounds.json)

## Verification and reproduction

Liu’s preprint gives the number-field theorem. For the Dirichlet case, Joseph Bebel’s tracker proof uses the same isolated root of the same degree-nine polynomial. Modulus one gives Riemann zeta. The tracker records the algebraic bound, its isolation and its rational comparison as passing three kernels. TheSil’s preceding Dirichlet bound was $`0.8733468`$. [Liu’s preprint record](https://hexagonmath.org/2611.00421v1) · [TheSil, PR 137](https://github.com/GTimG/QuasiRiemannTracker/pull/137) · [Bebel’s exact endpoint](https://github.com/GTimG/QuasiRiemannTracker/pull/143) · [Verifier run](https://github.com/GTimG/QuasiRiemannTracker/actions/runs/43761452075/attempts/1)

My Lean 4.19 proof matches the polynomial, specializes the Dirichlet statement to modulus one, transfers both sides of the strip to $`s`$, preserves multiplicity, and reflects a differentiable zero path. It also proves that the arithmetic quotient is nonzero. The transfer takes the all-Dirichlet theorem as an argument. Bebel’s certificate supplies that theorem in a separate Lean 4.34.1 build. The implicit derivative and Euler-product inequalities are the written proof above. [Local Lean declarations](../../lean/SuperZeta/Oriented/LiuEndpointTransfer.lean) · [Upstream Lean declarations at the verified commit](https://github.com/GTimG/QuasiRiemannTracker/blob/c74d855c3bdfceeee059501aea76c8b1627b9abd/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean)

From the repository root, run the following in a Python environment with Python 3.12 and python-flint 0.9.0. The script isolates the endpoint using exact rational Sturm arithmetic, checks the table at 256 bits, and computes both derivatives at each of the first ten zeros. For each it compares the Hurwitz derivative against a second evaluation using the Dirichlet $`L`$-function and $`\zeta'(\rho)`$. Both evaluations use FLINT. The eleven high-zero counts have separate certificates linked above. [Replay source](verify_angular_velocity.py) · [Lean setup](../../lean/README.md#run-the-proofs)

~~~sh
python archive/2026-11-20-liu-angular-velocity-v001/verify_angular_velocity.py
python tools/check_lean.py --fetch-cache
~~~

This deposit extends the [two-angle calculation of 19 November](../2026-11-19-oriented-return-v001/README.md). The Lean source comes from my 20 November file `LiuEndpointTransfer.lean` (source SHA-256 `f6a5b019556cc08bd925595c2280973d3c2d1293681078a43d1c10ae39612580`). The replay adapts the speed, root-isolation and Hurwitz-derivative calculations from `verify_turn_coordinates.py` (source SHA-256 `0419be11e99b3d2de8a89d082d0974c9ce98e3a56037dbaf24237e8eb7743a39`). The JSON records the inputs and enclosures for this version. [File hashes](manifest.json)
