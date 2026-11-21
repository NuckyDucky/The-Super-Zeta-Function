# Rebuilding the Gaussian circle calculation from the quartic’s signs

I use the quartic character to form a signed integer coefficient at each norm. The circle proofs use sums of these coefficients at 193 cutoffs. The command below starts at norm one, rebuilds the moment table, compares it with the deposited record, and runs the published circle proofs on the fresh values. Run it from the repository root with Python 3.12.

~~~sh
python -m pip install numpy==2.5.5 python-flint==0.9.0
python -B tools/rebuild_gaussian_evidence.py
~~~

The command uses four CPU workers by default. To use one, append `--workers 1`. The circle proofs read the rebuilt table from a temporary directory. To retain a fresh copy of just the table, run `python -B tools/gaussian_moments.py new-moments.json.gz`. [Full replay](../../tools/rebuild_gaussian_evidence.py) · [Coefficient and moment calculation](../../tools/gaussian_moments.py)

### From a lattice point to a moment

For $n=u^2+v^2$, I use one generator of each Gaussian ideal by taking $u\ge1$ and $v\ge0$. Each generator contributes the product of the three residue signs specified by my quartic. Their sum is $a_n$. At norm 73 the two terms have opposite signs, so $a_{73}=0$. Larger norms can have several generators with the same sign. Each one contributes before the signs at that norm are added. [Character and conductor](../../archive/2026-11-20-gaussian-reflected-disks-v001/gaussian_inputs.py)

At $s_0=1/2+iT_D$ the Taylor coefficients and the absolute mass used to bound the Taylor remainder are

$$
M_k(N)=\frac{1}{k!}\sum_{n=1}^{N}a_n n^{-s_0}(-\log n)^k,\quad 0\le k\le16,
\qquad
A(N)=\sum_{n=1}^{N}\frac{|a_n|}{\sqrt n}.
$$

The cutoff is $N=2^{26}+j\,2^{20}$ for $0\le j\le192$. At each cutoff I compare the number of nonzero coefficients and the SHA-256 digest of the entire ordered sequence, beginning with $a_0=0$ and writing each coefficient as a signed 32-bit little-endian integer. I also check the 27 individually recorded coefficients.

The deposited table used 192-bit ball arithmetic. The CPU rebuild uses 256 bits and requires the fresh interval for every real part, imaginary part and absolute mass to lie inside its published interval. The program compares the decimal endpoints as exact rational numbers. Across 193 cutoffs, that gives 6,755 interval comparisons. The circle proofs then read the fresh intervals. [Published moment record and formula](../../archive/2026-11-20-gaussian-circle-phases-v001/README.md#reproducing-the-circle-measurements)

### What the four replays check

| Calculation | Result checked |
| --- | --- |
| [Phase on both complete circles](../../archive/2026-11-20-gaussian-circle-phases-v001/replay.py) | At every cutoff the right circle misses the target phase by more than $0.91$ radians. The reflected circle reaches it twice in opposite directions. |
| [Omitted-term estimate](../../archive/2026-11-20-gaussian-circle-phases-v001/replay_tail.py) | The 384-bit calculation uses opposite-sign ideals at 404 split primes to reproduce the archived absolute remainder bound. This check has its own prime inputs. |
| [192 changes of cutoff](../../archive/2026-11-20-gaussian-relative-remainder-v001/verify.py) | 137 changes pass both the size and direction tests. A further 29 pass the direction test. The remaining 26 pass neither adjacent test. |
| [Common sector](../../archive/2026-11-20-gaussian-common-sector-v001/verify_sector.py) | The **maximum** angular width as the input moves around the right boundary is between $2.90$ and $2.92$ radians. The upper bound applies everywhere. The lower bound comes from a measured pair at one input. |

In the CPU replay through norm $268{,}435{,}456$, all 193 coefficient hashes and nonzero counts matched, and all 6,755 interval comparisons passed. The sector verifier covered the circumference with 865 arcs. At $\theta=537\pi/512$ it enclosed one pair’s angular separation at $2.904872079576\pm2.37\times10^{-13}$ radians.

Since $2.92<\pi$, the readings have a common positive projection at each boundary input. This lets me deform any fixed convex combination of the 193 finite functions to a reference whose winding is zero. The argument principle excludes zeros of that combination inside the disk. Reflection gives the result on the other disk. Both disks here have radius $31/2048$. The full Gaussian factor has a separate bound of at most seven zeros per closed disk of radius $15/1024$. Its exact count remains open. [Convex-family proof](../../archive/2026-11-20-gaussian-common-sector-v001/README.md) · [Full-factor count](../../archive/2026-11-20-gaussian-reflected-disks-v001/README.md)
