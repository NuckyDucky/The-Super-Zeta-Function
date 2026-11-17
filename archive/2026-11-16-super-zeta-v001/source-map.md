# Formula-specific source map

16 November 2026. This map separates the published framework, the retained
reciprocal inputs, and the deductions proved in this continuation. Local
primary-source snapshots have URL, size and SHA256 records under
[sources/root](sources/root/source-records.json) and
[sources/balance](sources/balance/source-records.json).

## Published inputs and their actual use

| Source | Exact published input used here | Current deduction and proof |
|---|---|---|
| [Voros, 2014, §1](https://arxiv.org/pdf/1403.4558) | A zero-set zeta \(\sum(w_k+w)^{-s}\), Mellin continuation, regularized determinants and their positive-integer derivative traces; §1 equations (1), (3)–(5). | [Shifted superzeta](research/shifted-superzeta.md), equations (1)–(13): the specific cosine determinant, residue \(B_nw^n/\pi\), determinant \(4E_\varepsilon(-w)\), and its controlled continuation. The zero set used is the reciprocal cosine spectrum. |
| [NIST DLMF 15.9.24](https://dlmf.nist.gov/15.9.E24) | \({}_2F_1(1/2,1/2;1;m)=2K(\sqrt m)/\pi\), with NIST's elliptic modulus convention. | [Residue period](research/residue-period-and-chords.md), equations (1)–(6): the squared residues form the specified Legendre period, pair-of-chords moment measure and Stieltjes transform. |
| [NIST DLMF 19.8](https://dlmf.nist.gov/19.8) | Gauss's arithmetic–geometric mean representation of the complete elliptic integral. | The residue period's explicit upper/lower AGM enclosures, including its logarithmic endpoint. |
| [NIST DLMF 20.9](https://dlmf.nist.gov/20.9) | Elliptic/theta identities \(K(k)=\pi\theta_3^2/2\) and \(k=\theta_2^2/\theta_3^2\). | \(\mathcal M(\lambda(\tau))=\theta_3^2\), where \(\lambda=k^2\), on the branch continued from positive imaginary \(\tau\); [period note](research/residue-period-and-chords.md), §4. |
| [NIST DLMF 5.17](https://dlmf.nist.gov/5.17); [5.11](https://dlmf.nist.gov/5.11) | Barnes recurrence \(G(z+1)=\Gamma(z)G(z)\), \(G(1)=1\), and positive-axis Barnes/Stirling asymptotics. | [Binomial normalization](research/binomial-normalization.md), equations (2)–(5): the exact finite product and \(N^{1/4}\) limit \(e^{\sin d/2}/G(3/2)^2\), with every initial and \(2\pi\) factor retained. |
| [DLMF 5.9.16](https://dlmf.nist.gov/5.9.E16) and [4.36.2](https://dlmf.nist.gov/4.36.E2) | Digamma integral and the hyperbolic-cosine product. | The positive kernel \(\log D_n=-\int e^{-nt}\tanh(t/4)dt/t\), its exact partial fractions, signed next-term remainder and finite-cutoff error; [normalization note](research/binomial-normalization.md), §§2–4. URLs are retained in [binomial source records](sources/binomial-primary-references.json). |
| [DLMF 25.2](https://dlmf.nist.gov/25.2) and [25.6](https://dlmf.nist.gov/25.6) | Riemann-zeta pole normalization, \(\zeta(0)=-1/2\), \(\zeta'(0)=-\log(2\pi)/2\). | [Deformed zeta](research/binomial-deformed-zeta.md): complete coefficient recurrence, pole leading parts, finite-part invariant and effective-spectrum determinant \(\sqrt{2\pi}e^{\sin d/2}/G(3/2)^2\). |
| [Guttmann, 2010, equations (1)–(6)](https://arxiv.org/pdf/1004.1435) | Lattice Green functions, step structure functions, constant terms and return probabilities. | [Balanced charge operators](research/balanced-charge-operators.md), §§1–2: the specific symmetric charge lift, anisotropic elliptic resolvent, \(B_n^2\) normalization and actual-quartet Bessel kernel. |
| [Ruelle, 1976, Theorem 1 and holomorphic trace lemma](https://www.ihes.fr/~ruelle/PUBLICATIONS/%5B45%5D.pdf) | Holomorphic function/one-form traces and Fredholm determinants for contracting inverse branches. | Four explicit certified inverse branches of \(g_{L_*}\), Hardy trace-class bounds, their trace difference equal to one per ordered word, and the charge/prime-clock extension; [operator note](research/balanced-charge-operators.md), §§3–8. |
| [Guido–Isola–Lapidus, 2006, §5](https://preprints.ihes.fr/storage/LapidusM39.pdf) | Analytic trace determinants in periodic graph settings, with a specified trace and logarithm branch. | The trace per lattice charge cell, the germ \(\operatorname{Det}_{\mathfrak T}\), and the relative zero-charge joint product \(\mathcal Q_{p,0}\). |
| [Lenart, 1996, §§1 and 3](https://fpsac-archive.github.io/FPSAC96/ARTICLES/32Lenart.pdf) | Necklace algebras, primitive words, the cyclotomic/ghost-coordinate construction and Frobenius/Verschiebung; credits Metropolis–Rota. | [Ordered histories](research/ordered-signed-histories.md), §§1–2 and 6: elementary balanced-necklace Möbius formulas, primitive Euler products, complementary-half odd-divisor count and actual composition operators. |
| [Viswanathan, 2020 version, §II equations (4)–(5)](https://arxiv.org/pdf/1706.00799) | The classical square-lattice entropy \(4G_{\rm Cat}/\pi\), with earlier Wu credit. | The specific normalized critical history zeta \(4e^{-4G_{\rm Cat}/\pi}\); [ordered histories](research/ordered-signed-histories.md), §3, includes its torus/log-sine derivation. |
| [Hu–Kim, 2018 version, introduction](https://arxiv.org/pdf/1703.05434) | The complex alternating multiple Barnes–Euler definition with parameter vector; the paper separately constructs its p-adic analogue for odd primes. | [Laplace–Barnes expansion](research/laplace-barnes-expansion.md), equations (2)–(7): exact occurrence of the complex coefficients, their finite eta reduction, coupling threshold and uniform tail. The coefficient calculation uses the complex definition. |

The elementary exponential derivative, Schwarzian and finite-word chain
rules used in [ordered histories](research/ordered-signed-histories.md) are
derived in that note. They yield the actual phase formula
\(\rho_w=\sum D_j^2/[3(\sum s_{j+1}D_j)^2]\), its cyclic invariance,
and the certified primitive \(++--\) example.

## Retained reciprocal inputs

| Retained input | Local proof/provenance | Role in this continuation |
|---|---|---|
| Complete multiplier-one phase classification, \(\alpha=e^{\pm t_n\pm i\theta_n}\), \(R_n=e^{t_n\coth t_n}\). | [Frozen parabolic locus](sources/balance/inputs/parabolic-locus.md). | Exact quartet weights, radius levels and independent phase/counting indices. |
| \(E_\varepsilon(\lambda)=\cos^2\sqrt\lambda-\lambda/\varepsilon^2\), boundary operator and trace-class inverse square. | [Frozen cosine-spectrum proof](sources/foundation/cosine-spectrum.md). | The current shifted superzeta's actual zero set and determinant normalization. |
| Exact radial product \(\prod R_n/(2\pi n)=e^{\sin d/2}\). | [Frozen radial-product trace theorem](sources/foundation/radial-product-trace-theorem.md), [radial zeta](sources/foundation/radial-zeta.md). | The reciprocal factor in the exact Barnes constant. |
| Controlled radial polynomials \(\chi_j\). | [Frozen coefficient input](sources/radial-coefficient-input.json), with original SHA256. | The finite-cutoff and deformed-zeta computations. |
| Quartet/finite-clock Fredholm product \(\mathcal Q_p\), radial sign flip \(r(\alpha)=1/\bar\alpha\), angular flip \(c(\alpha)=\bar\alpha\). | [Frozen clocked-transfer proof](sources/balance/inputs/clocked-transfer-spectrum.md). | The continuous two-character lift and its zero-charge extension. Reciprocity is the composed action \(rc\). |
| Direct p-adic orbit-ball and Fatou-cover clocks. | [Frozen earlier p-adic dynamics](sources/foundation/padic-dynamics.md), [frozen solenoidal clock](sources/foundation/solenoidal-clock.md), with their use specified in the frozen clocked-transfer input. | The current finite reductions are \(C_{p^k}\), updating at scalar-return completion. The retained-level product and the completed adding-machine trace have their separate exact definitions. |

The Laplace coordinate \(\nu\tanh\nu=1\),
\(R_{\rm L}=\nu/\cosh\nu\), is the imaginary critical section of the
published inverse-cosine framework used in the earlier 2024-frontier work.
Its new role here is proved directly: it is the maximum of
\(\sqrt v\,\operatorname{sech}\sqrt v\), the inverse-coupling expansion
threshold, and the coefficient saddle. The earlier 2024 source comparison
and variable-specific Borghi transfer are retained in the existing
2024-frontier proof in the separate Greater-Works-2024-Frontier package.

## Convention key

- Elliptic \(K(m)\) or \(\mathbf K(m)\) in this package uses the
  **parameter** \(m\). The NIST modulus is \(k=\sqrt m\). In a walk
  variable z the isotropic Green function is \(2K(z^2)/\pi\).
- \(K_\nu(x)\) in the shifted Bessel series is the modified Bessel
  function. The Barnes constant is \(e^{\sin d/2}/G(3/2)^2\), named K
  in its detailed note and \(C_*\) in the main report.
- The spectral shift w in \(\mathscr S\) is additive to \(u^2\).
  The exponent w in the detailed binomial-deformation note is named
  \(\beta\) in the main report.
- \(\varepsilon\) is the auxiliary inverse-cosine coupling; L is the
  exponential dynamical parameter. Quartet radii \(R_n\) and the Laplace
  constant \(R_{\rm L}\) retain their own definitions.
- The elliptic nome is \(q=e^{\pi i\tau}\). The primitive-history q
  marks half-length; its two-stream normalization is \(q=t/16\).
- The current \(\xi,\upsilon\) are Fourier characters of the two integer
  charges. The earlier Fatou-cylinder coordinate and its prime covers
  retain their definitions in the frozen solenoidal proof.

The earlier six-integer arithmetic curve and its descent keep their
coefficients and proofs in their arithmetic archive. The elliptic curve
in the present period calculation is explicitly the Legendre family
\(Y^2=x(1-x)(1-zx)\).
