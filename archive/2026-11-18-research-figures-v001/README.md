# Figures for the original meme and the Dottie spire

NuckyDucky supplied the original meme and the six integer coefficients. The Dottie spire comes from his study of the ordered reciprocal exponential iteration. The [main page](../../README.md#from-the-original-meme-to-the-dottie-spire) gives the reciprocal substitution and explains how the spire’s fold leads to the cosine determinant.

## The quadratic reconstruction of pi

The plot uses the original target $T(x)=(1+x)(2+x)/(x^2+x-1)$ and the rational function $R(e)$ with coefficients $(-659,-183,465;-936,396,155)$ in ascending powers of $e$, numerator first. Its intersection is the root $\widehat\pi$ of $T(x)=R(e)$ near $\pi$. In the figure the origin is $(\pi,T(\pi))$. One unit on either axis represents $10^{-20}$. A positive change in $T$ near $\pi$ corresponds to a negative change in $x$.

The drawing samples $T$ at 85 decimal digits using mpmath, then converts the centered coordinates to ordinary floating point for plotting. The plotted displacement agrees with the Lean-certified interval $8.682007272724\times10^{-20}<\pi-\widehat\pi<8.682007272726\times10^{-20}$. The actual approximation, to the digits shown, is $\widehat\pi=3.141592653589793238375823310552253\ldots$. [Original coefficients and quadratic inversion](../../lean/SuperZeta/Meme.lean) · [Lean error bound](../../lean/SuperZeta/MemePrecision.lean)

From this directory, reproduce the plot using Python 3 with Matplotlib 3.11.2 and mpmath 1.3.0.

~~~sh
python -m pip install matplotlib==3.11.2 mpmath==1.3.0
python plot_pi_hat.py pi-hat-reproduced.png
~~~

## The Dottie spire

For each parameter $L$ the numerical survey iterates $(P,Q)\mapsto(e^{LQ},e^{-LP})$ from $(1,1)$. The colors record the detected periods of this paired iteration. The label $L_*$ shows the exact fold parameter $i e^{-\sin d}$, where the Dottie number $d$ solves $d=\cos d$. The position of the fold is proved analytically. The image represents a finite survey of the surrounding parameter plane. [Spire paper and interval proofs](../2026-11-18-lean-foundations-v001/papers/dottie-spire/main.pdf) · [Fold in Lean](../../lean/SuperZeta/Dottie.lean)

Both panels use the lab’s **Layer 4 (Fine)** settings. Each panel was evaluated on its own grid, with four orbit samples per displayed raster pixel and a separate orbit at the center. The final PNG is **2540 × 1590**.

| View | $\Re L$ | $\Im L$ | Raster before layout |
| --- | --- | --- | ---: |
| Overview | $[-0.145,0.145]$ | $[0.492,0.748]$ | 1560 × 1120 |
| Detail near the tip | $[-0.0065,0.0065]$ | $[0.5085,0.5485]$ | 864 × 1120 |

The calculation uses CUDA binary64, an iteration limit of 8000, a maximum candidate paired period of 256, and a tolerance of $10^{-10}$ for repeated laps. Gray means the calculation reached its limit without assigning a period. The period-320 parameters used for the zeta height are verified separately with 384-bit interval arithmetic. [Render settings, source hashes and sampled counts](dottie-spire-render.json) · [Period-320 calculation](../2026-11-18-lean-foundations-v001/checks/dottie_slice.py)

On an NVIDIA CUDA-capable GPU, the renderer can use the bundled copies of the lab’s three numerical modules. From this directory run the following commands to save a new copy in a separate directory.

~~~sh
python -m pip install -r lab_source/requirements.txt
python -B render_dottie_spire.py --output-directory reproduced-spire
~~~

The JSON result records the hardware, numerical limits, sample counts and PNG hash. The figure shows the classification at the sampled coordinates.
