# Two critical-line zeros across the full strip in the Dottie height window

17 November 2026. This addendum extends the [matched Dottie and grid experiment](../2026-11-17-dottie-grid-match-v001/README.md). The extension combines its finite contour certificate with OpenAI's global seven-eighths theorem. The two-thirds calculation below separately tests how the marked quartet addresses compare with a measured zeta magnitude.

## Full-strip corollary

Let $w=\beta+it=2s$ be the Riemann coordinate. The exact Dottie height used here is

$$
T_D=\frac{2\pi}{160\log(1+(x/y)^2)},\qquad
x=4.749479070945369\times10^{-8},\quad y=0.509892982511772.
$$

The decimals specify exact rationals. The predecessor's finite witnesses give 320 occurrences of the marked arrow in 640 ordered exponential stages. With the frozen one-winding convention, $T_D=4526119322477.945393319207\ldots$.

**Result.** The region $0<\beta<1$, $|t-T_D|<1/4$ contains exactly two zeros of $\zeta$, both simple and on $\beta=1/2$. In the superzeta coordinate their real part is $1/4$, and the height window is $|\Im s-T_D/2|<1/8$. The reconstructed function $\mathcal Z(s;1)-J(s;1)=2\pi^{-2s}(2^{2s}-1)\zeta(2s)$ has the same zero multiplicities there. [Spectral reconstruction, eq. 21](../2026-11-16-super-zeta-v001/sources/foundation/cosine-spectrum.md)

**Proof using the archived certificate.** OpenAI's Theorem 1.1 excludes zeros with $\beta>7/8$ at every height. The functional equation and complex conjugation take a nontrivial zero at $\beta+it$ to $1-\beta+it$, which excludes $\beta<1/8$ as well. The entire remaining closed interval $[1/8,7/8]$ lies strictly inside the already counted interval $(1/16,15/16)$. Both boundary lines of the global bound are therefore covered. [OpenAI, Theorem 1.1, p. 4](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) · [Riemann reflection](https://dlmf.nist.gov/25.4)

At 192 bits, the two contour pieces had counts one and one, including a zero-free shared edge at $t=T_D$. Two disjoint Hardy sign brackets on $\beta=1/2$ each enclose at least one zero. Together they exhaust the total count with multiplicity. The certified signed separation squared is in $[-0.019772414113648,-0.019772412018329]$. Its negative sign records two distinct heights. The analytic prefactor in the reconstruction is nonzero for $0<\Re(2s)<1$. This proves the corollary. The gain over Theorem 1.1 is the exclusion of **all** off-line zeros in this specific height window. At other heights the global theorem leaves the right-hand interval $(1/2,7/8]$ open to an RH counterexample. [Frozen boxes](../2026-11-17-dottie-grid-match-v001/dottie-grid-forecast.json) · [Directed count and line brackets](../2026-11-17-dottie-grid-match-v001/dottie-grid-certificate.json)

## What the two-thirds rule selects

At level $n$, the four marked entries are $b_{\sigma,\tau}(w)=C_n^{-w/2}\exp((w-1/2)(\sigma t_n+i\tau\theta_n)/2)$, where $\sigma,\tau\in\{-1,+1\}$. The ratio between the two radial marks at fixed $\tau$ has magnitude $r_n(u)=\exp((u-1/2)t_n)$ with $u=\Re w$. The radial correction $C_n$ cancels. Solving $r_n(u)=2/3$ and reflecting to the right gives

$$
\beta_n=1-u=\frac12+\frac{\log(3/2)}{t_n}.
$$

The spectrum has strictly increasing $t_n\to\infty$. Thus $\beta_n\downarrow1/2$, with $\beta_n\leq\beta_1<0.7240929432$ at every level. Already $\beta_2<2/3$, so the same holds for every $n\ge2$. These inequalities locate the **candidate addresses selected by this rule**. Applying them to every off-line Riemann zero would require a proof that every such zero satisfies the marked-ratio rule. For the completed four-tag matrix the determinant is $\xi(w)^4 C_n^{-2w}$, since the four signed logarithms sum to zero. Its common zeros are consequently selected by $\xi(w)=0$. [Quartet classification and monotonicity](../2026-11-16-super-zeta-v001/sources/balance/inputs/parabolic-locus.md)

The separate observable $|\zeta(\beta+iT_D)|/|\zeta(1/2+iT_D)|$ crosses $2/3$ at a point in $(0.542962564820,0.542962564824)$. Directed signs at the endpoints and continuity certify existence in this bracket. To attain the marked ratio at that same displacement requires $t=\log(3/2)/(\beta-1/2)$. Inverting the quartet phase equation puts its continuous level strictly between $1997$ and $1998$, at about $1997.71526$. The two integer levels give marked ratios $0.6666769235$ and $0.6666625846$, respectively, rounded here. Thus there is no common crossing at an integer level in this bracket. [Directed verification output](replay-results.txt)

## Replay and recovery

The archive retains the original slice and quartet verification scripts byte for byte. The [replay entry point](replay.py) cross-checks the frozen input hashes, recomputes the full Dottie arm, compares it with the archived numerical record and runs both new checks. The local proof uses Theorem 1.1 as an external input. The contour uses two charts with 144 circular samples each at 192 bits. The horizontal slice uses 80 samples and analytic truncation control at 192 bits. The quartet translation uses 224 bits and 108 bisections per integer level. All inputs are deterministic.

From the root of a fresh checkout, using Python 3.12.11 and the predecessor's pinned dependencies, run

```text
python -m pip install -r archive/2026-11-17-offcenter-superzeta-v001/requirements.txt
python -B archive/2026-11-17-dottie-local-strip-v001/replay.py
python tools/verify_archive.py
```

Compare stdout with [the saved run](replay-results.txt). The [provenance record](provenance.json) identifies the source inventory and runtime. The milestone tag is `dottie-local-strip-v001`. [Archive recovery procedure](../../PRESERVATION.md)
