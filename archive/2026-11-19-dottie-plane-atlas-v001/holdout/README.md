# A forward test from two consecutive elementary seeds

I chose the seventh and eighth positive zeros of the factor $3^w-1$ as starting points. The two resulting paths initially turned in opposite directions. Their endpoints were also different. The seventh seed reached the fifth positive elementary zero of $2^w-1$. The eighth seed reached the **eleventh Riemann zero**, beyond the ten landings in the earlier study. The protocol appeared on GitHub before I evaluated either path. [Original public protocol](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/a739bf30c0db09774d4fd3681596a1821f31d081/protocols/2026-11-19-dottie-plane-holdout.json)

| Seed at 60° | Horizontal displacement after a quarter-degree | Certified endpoint at 45° | Final complex error from the quadratic forecast |
| --- | ---: | --- | ---: |
| $14\pi i/\log 3$ | $-0.04714487$ | $10\pi i/\log 2$, height 45.323601418272 | 0.00001901003122 |
| $16\pi i/\log 3$ | $+0.20731832$ | $\rho_{11}$, height 52.970321477714 | 0.00030670982748 |

The signed launch forecast used only the initial tangent, whose real part was approximately $-0.229539$ for the first seed and $+0.836759$ for the second, per clockwise degree. I then followed each marked Hurwitz zero to one eighth of a degree before the end. At that cutoff I predicted the final complex coordinate from position, tangent, and acceleration. Both predictions met the preselected tolerance of **0.001**. The unchanged-position and tangent controls both missed this tolerance on both seeds. [Sealed launch forecasts](launch.json) · [Sealed endpoint forecasts and cutoff positions](forecast.json) · [Errors and controls](score.json)

Before the endpoint computation, the two quadratic forecasts were respectively $-0.0000080662+45.3235842044i$ and $0.4996965181+52.9703658587i$. Both called the correct endpoint type using the threshold $\Re w=1/4$. Applying that same threshold to the cutoff positions also gives the correct types on these two cases. The measurable improvement is the complex coordinate error. The forecast runs used forward information through the cutoff. The ordinal eleven was identified by the subsequent independent comparison. [Final disks](terminal.json) · [Endpoint identifications](score.json)

The equation was $H(w,b)=\zeta(w,b)+\zeta(w,1-b)=0$, with $b=1/6+h/180$ for $h$ clockwise degrees. The start and end factorizations follow by grouping Dirichlet series into residue classes and analytically continuing

$$
H(w,1/6)=(2^w-1)(3^w-1)\zeta(w),\qquad H(w,1/4)=2^w(2^w-1)\zeta(w).
$$

The continuation used 612 and 567 accepted contracting tubes. Each final disk had radius $10^{-24}$. Only after the two terminal disks had been sealed did I compare them with independently evaluated elementary addresses and ordinary Riemann zero enclosures. The family and its rational endpoint factorizations predate this experiment. [Published history of the symmetric Hurwitz paths](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/5c5f3a160b2412a49b0b1e86fa24f7605a938823/archive/2026-11-19-zero-transport-v001/Dottie-Transport-Reversibility/PRIOR-WORK.md)

### What happens to nearby points?

After scoring, I used the same local map as in the heatmap. Let $u=\Phi(w)$ be the endpoint of a nearby point transported at the same value of the unweighted $H$. From $H(\Phi(w),1/4)=H(w,1/6)$ it follows that $\Phi'(w)=H_w(w,1/6)/H_w(u,1/4)$. Around seed 7 the full turn stretches small displacements by a factor of **1.181197** and turns them **+66.346°**. Around seed 8 it scales them by **0.511244** and turns them **−130.568°**. These are local length ratios and orientations modulo 360°. Over just the final eighth of a degree, both neighborhoods expand slightly. The newly tested branches show why the start and end angles matter when interpreting a color on the map. [Post-score geometric calculation](local_scale.py) · [Enclosed length ratios and angles](local_scale.json)

## Reproduce the four stages

From this directory in a full repository checkout, use Python 3.12 and python-flint 0.9.0. The verifier imports the centered interval tube algorithm from the public zero-transport archive. Keep the four generated records together in a fresh directory.

```sh
python -m pip install python-flint==0.9.0
python -B holdout.py launch --freeze-commit a739bf30c0db09774d4fd3681596a1821f31d081 --out replay
python -B holdout.py forecast --out replay
python -B holdout.py terminal --out replay
python -B holdout.py score --out replay
python -B local_scale.py --dir replay
```

| Record | SHA-256 |
| --- | --- |
| Public protocol | `8ab949c14e7edb66d59dbe91da6d3bb8a252ec7857b45a9129986e0ec9b7c7cb` |
| Launch | `8a70d31c772a0ac6b15b2b7a3cdbf186d982589a7bc57fda7e0d5bdc1d65676d` |
| Forecast | `385021ce89f4f5fb278375c8fe7a5f5bc84dee47efa93c0a6534b3240b002b37` |
| Terminal disks | `e2bf3861f38db4aeb99032212f820a5af9969c223e88be7496873f0bcfa45287` |
| Score | `3d047fcfe34b25d12483436a4750abe718d53572044d33ef9a995f8e54b9d11c` |
