# How many Gaussian zeros can the two reflected disks contain?

At height $T=T_D-1/512$, I tested two disks of radius $15/1024$ centered at $31/64+iT$ and $33/64+iT$. The right disk comes within $1/1024$ of the critical line. Reflection across that line sends it onto the left disk and preserves the multiplicity of every zero of my quartic field’s completed Gaussian factor. A single zero in either disk would therefore give a pair of off-line zeros at the same height. The current upper bound is seven in each closed disk. The winding count of the complete function remains unresolved. [Field, character, and functional equation](../2026-11-20-gaussian-endpoint-parity-v001/gaussian-hardy-endpoints.md)

## How the arithmetic rules out eight per disk

The Weil explicit formula assigns a nonnegative weight to every nontrivial zero throughout the critical strip. I chose a weight that exceeds $5.481507$ wherever $|\Im w-T|\le15/1024$. The conductor, gamma factor and signed prime-ideal powers give a total weight below $87.057901$. Eight zeros on the right would give eight on the left, and those sixteen alone would contribute more than

$$
16(5.481507)=87.704112.
$$

This exceeds the total even before accounting for any other zeros. The same calculation bounds the entire closed horizontal band by fifteen, with multiplicity. It uses positivity on the full strip, including off-line inputs. [Derivation and numerical constants](mass-proof.md) · [192-bit arithmetic record](mass-count.json) · [160-bit calculation with a second gamma bound and a different cutoff](fourier-count-2pow23.json)

The earlier $1/7$ measures the amplitude of a character reading. Applied to the order-two Dirichlet character $\chi_{-3}$, the detector $1+\chi_{-3}(p)^k/7$ gives $8/7$ or $6/7$ at unramified prime powers. Here the arithmetic sum uses the quartic field’s Gaussian ideal character $\eta_\delta(\mathfrak p)^k$, and the integer seven comes from taking the floor of the trace bound divided by twice the minimum weight per zero. With the same two disks, the shorter cutoff $2^{20}$ in the second calculation gives eight per disk and $2^{23}$ gives seven. [Earlier prime-weight construction](../2026-11-20-cap-derivative-recovery-v001/README.md) · [Shorter cutoff](fourier-count.json)

## What the circle calculation resolves

The finite smoothed contributions have winding zero at all four reported cutoffs. Their real parts can change sign as more Gaussian norms enter. At $N=262144$ the entire finite boundary lies in the left half-plane, while at $N=1048576$ it lies in the right half-plane. Every enclosure of the **full** boundary still contains zero after the omitted terms are included. [Arc proof and finite controls](arc-method.md)

**Open question.** Can the signed coefficients in the omitted terms give a uniform upper bound

$$
\sup_{s\in\partial D_R}\Re R_{262144}(s)<7.6098\times10^{-29}
$$

in the positive scaling $B^2|\Gamma(2+iT_D)|$? Here $R_N$ is the complete scaled function minus the exact smoothed finite contribution. That finite contribution has real part below $-7.6098\times10^{-29}$ on the entire circle. The proposed upper bound would keep the full boundary in the open left half-plane. The argument principle would then give zero zeros in the right disk, and reflection would clear its mirror. The current absolute bound on the omitted terms is $2.312\times10^{-17}$. [Record at the stated cutoff](arc-gaussian-262144-64.json)

## Reproduce the eight records

Use Python 3 and install [python-flint 0.9.0](https://pypi.org/project/python-flint/0.9.0/) in the environment. From this directory run

~~~sh
python -B replay.py
~~~

The replay recomputes five contour records (the first 64-arc attempt at $N=65536$ and its 512-arc refinement are both retained), two Fourier cutoff records, and the $10^7$ prime-power calculation. It compares all saved JSON values, including every arc, before checking the bounds above. It writes fresh records to a temporary directory. The [height and Gaussian ideal signs](gaussian_inputs.py) are included from the [endpoint calculation](../2026-11-20-gaussian-endpoint-parity-v001/gaussian_inputs.py). The two prime-sum programs share these field data and the explicit formula. They compute the gamma bound and the prime sums separately.
