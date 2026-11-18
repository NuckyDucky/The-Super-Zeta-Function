# An off-center superzeta zero count

Research date 17 November 2026. This deposit extends the [quartet-return and coupling notes](../2026-11-17-quartet-return-recursion-v001/README.md). It compares a finite two-dimensional prediction, a certified count for the reconstructed superzeta response, and a separately counted cosine-determinant control.

## Windows

Use $w=\beta+i(H+y)$ and $s=w/2$. For each level $n$, set $H=n\pi-d$ by solving $(n\pi-d)\tan d=(1/4)/\tanh(1/4)$. Set $\varepsilon=H/(\cos d\cosh(1/4))$. The selected cosine root is $H+i/4$. Each window has $-1/8<y<1/8$. The broad real interval is $1/16<\beta<15/16$. The right off-center interval is $5/8<\beta<7/8$.

## Methods

- **Finite prediction.** The degree-48 polynomial uses 691,008 finite reference modes for each level, the dyadic phase step, a Riemann–Siegel leading correction, and floating-point roots. The frozen JSON records predicted root locations within the broad window. Its roots are numerical forecasts.
- **Reconstructed response.** The [prior derivation](../2026-11-17-quartet-return-recursion-v001/quartet-return-phase.tex) identifies the coupling derivative at the reference point as $w(w-1)\pi^{-w}(2^w-1)\zeta(w)$. The prefactor has no zeros or poles in the three windows. The certificate therefore uses separate 192-bit directed samples of $\zeta(w)$ and a Cauchy bound on the error of the 144-node interpolant. The sample radius is $3/8$ and the outer bound uses radius $9/10$, with the error controlled out to radius $47/100$. Ball arithmetic translates the polynomial to nearby dyadic centers for evaluation. Outward-rounded enclosures cover each whole contour segment. The argument principle counts zeros with multiplicity. The number of disjoint Hardy sign brackets gives a certified lower bound for zeros on $\beta=1/2$.
- **Cosine control.** The original determinant $\cos^2u-(u/\varepsilon)^2$ is evaluated at $u=H+y+i(1/2-\beta)$. At the selected coupling the conjugate cosine root $H-i/4$ lies in the off-center window. The determinant has its own directed contour count. The verifier also places a narrow box around the cosine control at $(\beta,y)=(3/4,0)$ and certifies one zero there. A forecast with $\beta>1/2$ gets its own right-of-line narrow box for the reconstructed response.

## Signed pair test

For a completion $F$ that is real on the height axis, split the expansion at a real height offset $h$ as $F(h+i\sqrt q)=U+i\sqrt q\,V$ in the even and divided odd terms. Simultaneous zeros encode a same-height reflected pair when $q>0$ and two distinct line heights when $q<0$. At $q=0$ the conditions become $F(h)=F'(h)=0$.

The [signed prediction](offcenter-superzeta-signed-prediction.json) comes from the frozen degree-48 model. Its first adjacent pair yields $q=-0.0012657969184217206$. The sign specifies two different heights on the critical line. The directed certificate supplies disjoint line brackets, from which the checker derives a rational interval for $q$ using the squared half-separation.

## Results

| Level | Predicted roots in broad window | Certified reconstructed zeros in broad window | Disjoint line brackets | Reconstructed zeros in right window | Cosine zeros in right window |
| --- | --- | --- | --- | --- | --- |
| 954985468717 | 2 | 2 | 2 | 0 | 1 |
| 954985468718 | 0 | 0 | 0 | 0 | 1 |
| 954985468719 | 1 | 1 | 1 | 0 | 1 |

At each sampled level, the line brackets account for every zero in the broad window. The off-center count is zero for the reconstructed response and one for the cosine control. The uniform interpolation error is below $4.429\times10^{-16}$ in all three windows.

For the first pair, the signed separation check gives $-1425160827601/1125899906842624\le q\le -22802563691209/18014398509481984<0$.

[Frozen forecasts](offcenter-superzeta-prediction.json) · [Directed certificate](offcenter-superzeta-recentered-certificate.json)

## Replay

Copy this snapshot to a new scratch directory. Use Python 3.12 and the [recorded dependencies](requirements.txt). From the scratch directory run these commands. Output names must be new.

```text
python -m pip install -r requirements.txt
python -B offcenter_superzeta.py predict prediction-replay.json
python -B offcenter_superzeta.py check offcenter-superzeta-prediction.json certificate-replay.json
python -B signed_superzeta_split.py predict offcenter-superzeta-prediction.json signed-prediction-replay.json
python -B signed_superzeta_split.py check offcenter-superzeta-signed-prediction.json offcenter-superzeta-recentered-certificate.json
```

The count and signed replays read the frozen prediction so their output refers to the archived SHA-256. For a new forecast, the optional predict arguments select a first level and the number of consecutive levels. The [provenance record](provenance.json) lists the source checksums and the [manifest](manifest.json) covers the complete deposit.
