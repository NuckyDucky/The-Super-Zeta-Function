# The phase of the signed Gaussian sum on two reflected circles

I used the signs from my quartic to ask whether adding more Gaussian ideal norms can close a gap in the phase on the right circle. At each of 193 cutoffs, the finite sum stays more than **0.91 radians** from my chosen phase of 3.9 radians everywhere on the right circumference. On its mirror the same phase occurs twice. As I move counterclockwise around the right circle and reflect each input onto the left, the first left crossing has negative phase derivative and the second has positive derivative.

## The sum and the two circles

I used $w=33/64+i(T_D-1/512)+(31/2048)e^{i\theta}$ and $w^*=1-\overline w$. The cutoffs are $N=2^{26}+j2^{20}$ for $j=0,\ldots,192$. If $a_n$ is the sum of the quartic character signs over Gaussian ideals of norm $n$, put $S_N(w)=\sum_{n\le N}a_n n^{-w}$. With $A(w)=B^w\Gamma(w)/(B^2|\Gamma(2+iT_D)|)$ and $B=\sqrt Q/(2\pi)$, the two residues of the smoothed functional equation give the finite sum

$$
F_N(w)=A(w)S_N(w)+\overline{A(w^*)S_N(w^*)},
\qquad L_N(w)=F_N(w)/A(w).
$$

I measured $\arg L_N-\kappa\log|L_N|$ modulo $2\pi$, with $\kappa$ the ratio of the principal argument of the period-640 multiplier to its log modulus. The 3.9-radian target was chosen during exploration. I enclosed all input angles on each circle at each recorded cutoff. [Quartic signs and height](../2026-11-20-gaussian-reflected-disks-v001/gaussian_inputs.py) · [Derivation of the two residues](../2026-11-20-gaussian-reflected-disks-v001/arc-method.md) · [Multiplier intervals](../2026-11-19-dottie-plane-atlas-v001/atlas/phase_lift.json)

## Why the two crossings preserve the zero count

The right phase avoids 3.9 radians throughout one circuit. Its total change equals the change of $\arg L_N$, since $\log|L_N|$ returns to its starting value. The right finite winding is therefore zero. Reflection of the completed sum gives $F_N(w^*)=\overline{F_N(w)}$. The gamma factor is holomorphic and nonzero on both closed disks, so the left winding is zero as well. The two left crossings have opposite signs. Their appearance under the same phase test is consistent with $L_N(w^*)=\overline{A(w)}\,\overline{L_N(w)}/A(w^*)$.

To transfer this count to the full Gaussian factor using Rouché’s theorem, a sufficient bound is $|F-F_N|<|F_N|$ everywhere on the outer circumference. At the eastern point with $N=2^{28}$, $|F_N|$ is about $1.879\times10^{-28}$. The uniform upper bound available for the remainder is $7.558\times10^{-19}$ in the same completed units. The signed tail and the full disk count remain open. [Uniform bound](tail-bound.json) · [Tail calculation](replay_tail.py)

## Reproducing the circle measurements

From this directory, with Python 3.12 and python-flint 0.9.0, run

```text
python -B replay.py --cutoff 268435456
python -B replay.py
python -B replay_tail.py
```

The first command checks both complete circles at the last cutoff. The second applies the same test to all 193 cutoffs. The replay starts with 256 arcs per circle at 192-bit precision, bisects until it can enclose the phase, and checks strict monotonicity wherever a left arc can meet the target. The last command recomputes the 384-bit absolute tail estimate, using cancellation at 404 split primes. [Circle replay](replay.py) · [Archived gamma and Taylor bounds](../2026-11-20-gaussian-reflected-disks-v001/arc-gaussian.py)

The replay starts from the recorded coefficient sums. The compressed file contains the original interval moments, mass bounds, and cumulative SHA-256 hashes of the signed integer coefficients. For an independent calculation, the $k$th stored moment at $s_0=1/2+iT_D$ is $\sum_{n\le N}a_n n^{-s_0}(-\log n)^k/k!$, for $0\le k\le16$. The mass is $\sum_{n\le N}|a_n|n^{-1/2}$. The linked norm enumeration gives the signs directly. These are directed numerical checks. [Moment inputs](moments.json.gz) · [Gaussian norm enumeration](../2026-11-20-gaussian-reflected-disks-v001/arc-gaussian.py)

I deposited these calculations on November 20, 2026. The original filenames were `gaussian_signed_fine_moments.json` (stored with lossless gzip compression) and `gaussian_circle_tail.2p28.json` (stored as `tail-bound.json`). The SHA-256 of the decompressed moment record is `f014787ec40bba8df2786ba7cfb9b011a99152e6887c07b4dcc97f2a73d22c5d`. The replay uses the same archived Dottie height, multiplier and Gaussian normalization as the original runs.
